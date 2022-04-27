// SPDX-License-Identifier: GPL-2.0
#include <linux/tcp.h>
#include <net/tcp.h>

void tcp_mark_skb_lost(struct sock *sk, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tcp_skb_mark_lost_uncond_verify(tp, skb); // 丢失标记
	if (TCP_SKB_CB(skb)->sacked & TCPCB_SACKED_RETRANS) {// 此报文被重传过，既然已经丢失
		/* Account for retransmits that are lost again */
		TCP_SKB_CB(skb)->sacked &= ~TCPCB_SACKED_RETRANS; // 清除其重传状态位TCPCB_SACKED_RETRANS
		tp->retrans_out -= tcp_skb_pcount(skb);           // 将套接口重传计数retrans_out减去报文数量
		NET_ADD_STATS(sock_net(sk), LINUX_MIB_TCPLOSTRETRANSMIT,
			      tcp_skb_pcount(skb));
	}
	/*
	 * 重传报文再度丢失的情况下,sacked状态位为:(TCPCB_LOST|TCPCB_EVER_RETRANS),没有标志位TCPCB_SACKED_RETRANS。
	 */
}

static bool tcp_rack_sent_after(u64 t1, u64 t2, u32 seq1, u32 seq2)
{
	return t1 > t2 || (t1 == t2 && after(seq1, seq2));
}

// 返回乱序窗口
static u32 tcp_rack_reo_wnd(const struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (!tp->reord_seen) {
        // 当前套接口没有观察到乱序发生
		/* If reordering has not been observed, be aggressive during
		 * the recovery or starting the recovery by DUPACK threshold.
		 */
		if (inet_csk(sk)->icsk_ca_state >= TCP_CA_Recovery)
		    // 当前处于拥塞恢复状态（TCP_CA_Recovery）或者TCP_CA_Loss拥塞丢失状态，
            // 返回乱序窗口零，以便尽快的确认丢失报文，触发重传
			return 0;

		if (tp->sacked_out >= tp->reordering &&
		    !(sock_net(sk)->ipv4.sysctl_tcp_recovery & TCP_RACK_NO_DUPTHRESH))
		    // 拥塞状态不处于以上的两种状态，RACK开启了DUPTHRESH的支持，
		    // 并且SACK确认报文数量超过了乱序等级，很有可能发生了丢包，
		    // 接下来可能会进入TCP_CA_Recovery或者TCP_CA_Loss状态，
		    // 也返回值为零的乱序窗口，以便RACK作出快速响应
			return 0;
	}

	/* To be more reordering resilient, allow min_rtt/4 settling delay.
	 * Use min_rtt instead of the smoothed RTT because reordering is
	 * often a path property and less related to queuing or delayed ACKs.
	 * Upon receiving DSACKs, linearly increase the window up to the
	 * smoothed RTT.
	 */
	// 返回正常的乱序窗口
	return min((tcp_min_rtt(tp) >> 2) * tp->rack.reo_wnd_steps,
		   tp->srtt_us >> 3);
}

s32 tcp_rack_skb_timeout(struct tcp_sock *tp, struct sk_buff *skb, u32 reo_wnd)
{
	return tp->rack.rtt_us + reo_wnd -
	       tcp_stamp_us_delta(tp->tcp_mstamp, tcp_skb_timestamp_us(skb));
}

/* RACK loss detection (IETF draft draft-ietf-tcpm-rack-01):
 *
 * Marks a packet lost, if some packet sent later has been (s)acked.
 * The underlying idea is similar to the traditional dupthresh and FACK
 * but they look at different metrics:
 *
 * dupthresh: 3 OOO packets delivered (packet count)
 * FACK: sequence delta to highest sacked sequence (sequence space)
 * RACK: sent time delta to the latest delivered packet (time domain)
 *
 * The advantage of RACK is it applies to both original and retransmitted
 * packet and therefore is robust against tail losses. Another advantage
 * is being more resilient to reordering by simply allowing some
 * "settling delay", instead of tweaking the dupthresh.
 *
 * When tcp_rack_detect_loss() detects some packets are lost and we
 * are not already in the CA_Recovery state, either tcp_rack_reo_timeout()
 * or tcp_time_to_recover()'s "Trick#1: the loss is proven" code path will
 * make us enter the CA_Recovery state.
 */
// 丢失报文检查
static void tcp_rack_detect_loss(struct sock *sk, u32 *reo_timeout)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *skb, *n;
	u32 reo_wnd;

	*reo_timeout = 0;
	reo_wnd = tcp_rack_reo_wnd(sk); // 获取乱序窗口
	// 遍历tsorted时间排序的报文链表
	list_for_each_entry_safe(skb, n, &tp->tsorted_sent_queue,
				 tcp_tsorted_anchor) {
		struct tcp_skb_cb *scb = TCP_SKB_CB(skb);
		s32 remaining;

		/* Skip ones marked lost but not yet retransmitted */
		if ((scb->sacked & TCPCB_LOST) &&
		    !(scb->sacked & TCPCB_SACKED_RETRANS)) // 如果其已经被标记为丢失，但是还没有重传，不进行处理
			continue;

		/*
		 * 如果发送时间靠后的报文已经被确认（ACK或者SACK），那么之前的未确认报文认为已经丢失。
		 * 为抵御乱序的情况，RACK在确认报文和丢失报文之间设置了一定的时间差值。
		 */
		if (!tcp_rack_sent_after(tp->rack.mstamp,
					 tcp_skb_timestamp_us(skb),
					 tp->rack.end_seq, scb->end_seq))
			break;

		/* A packet is lost if it has not been s/acked beyond
		 * the recent RTT plus the reordering window.
		 */
		/*
		 * 当前报文的发送时间戳加上最近测量的RTT和乱序窗口时长，小于当前TCP时间，即认为此报文已经丢失
		 * tcp_rack_reo_wnd将乱序窗口时长设置为0时，报文更容易被认定为丢失
		 */
		remaining = tcp_rack_skb_timeout(tp, skb, reo_wnd); //计算报文剩余时间
		if (remaining <= 0) { // 报文剩余时间小于等于0，表明已经超时
			tcp_mark_skb_lost(sk, skb); // 标记报文丢失
			list_del_init(&skb->tcp_tsorted_anchor);
		} else {
			/* Record maximum wait time */
			*reo_timeout = max_t(u32, *reo_timeout, remaining); // 计算超时时长，返回给调用函数设置定时器
		}
	}
}

void tcp_rack_mark_lost(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 timeout;

	if (!tp->rack.advanced)
		return;

	/* Reset the advanced flag to avoid unnecessary queue scanning */
	tp->rack.advanced = 0;
	tcp_rack_detect_loss(sk, &timeout); // 标记丢失报文，获取超时时间值
	if (timeout) {
        // 返回timeout表示数据包rack标记loss时还未超时，返回剩余时间
        // 剩余时间作为timeout超时时间，启动reo_timeout定时器
		timeout = usecs_to_jiffies(timeout) + TCP_TIMEOUT_MIN;
		// 设置重传队列中报文超时的定时器ICSK_TIME_REO_TIMEOUT，
		// 由定时器tcp_rack_reo_timeout处理
		inet_csk_reset_xmit_timer(sk, ICSK_TIME_REO_TIMEOUT,
					  timeout, inet_csk(sk)->icsk_rto);
	}
}

/* Record the most recently (re)sent time among the (s)acked packets
 * This is "Step 3: Advance RACK.xmit_time and update RACK.RTT" from
 * draft-cheng-tcpm-rack-00.txt
 */
void tcp_rack_advance(struct tcp_sock *tp, u8 sacked, u32 end_seq,
		      u64 xmit_time)
{
	u32 rtt_us;

	rtt_us = tcp_stamp_us_delta(tp->tcp_mstamp, xmit_time);
	if (rtt_us < tcp_min_rtt(tp) && (sacked & TCPCB_RETRANS)) {
		/* If the sacked packet was retransmitted, it's ambiguous
		 * whether the retransmission or the original (or the prior
		 * retransmission) was sacked.
		 *
		 * If the original is lost, there is no ambiguity. Otherwise
		 * we assume the original can be delayed up to aRTT + min_rtt.
		 * the aRTT term is bounded by the fast recovery or timeout,
		 * so it's at least one RTT (i.e., retransmission is at least
		 * an RTT later).
		 */
		return;
	}
	tp->rack.advanced = 1;
	tp->rack.rtt_us = rtt_us;
	if (tcp_rack_sent_after(xmit_time, tp->rack.mstamp,
				end_seq, tp->rack.end_seq)) {
		tp->rack.mstamp = xmit_time;
		tp->rack.end_seq = end_seq;
	}
}

/* We have waited long enough to accommodate reordering. Mark the expired
 * packets lost and retransmit them.
 */
void tcp_rack_reo_timeout(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 timeout, prior_inflight;

	prior_inflight = tcp_packets_in_flight(tp);
	tcp_rack_detect_loss(sk, &timeout); // 标记丢失报文
	if (prior_inflight != tcp_packets_in_flight(tp)) {
		if (inet_csk(sk)->icsk_ca_state != TCP_CA_Recovery) {
			tcp_enter_recovery(sk, false);
			if (!inet_csk(sk)->icsk_ca_ops->cong_control)
				tcp_cwnd_reduction(sk, 1, 0);
		}
		tcp_xmit_retransmit_queue(sk);// 进行立即重传
	}
	if (inet_csk(sk)->icsk_pending != ICSK_TIME_RETRANS)
		tcp_rearm_rto(sk); // 重新调度RTO定时器
}

/* Updates the RACK's reo_wnd based on DSACK and no. of recoveries.
 *
 * If DSACK is received, increment reo_wnd by min_rtt/4 (upper bounded
 * by srtt), since there is possibility that spurious retransmission was
 * due to reordering delay longer than reo_wnd.
 *
 * Persist the current reo_wnd value for TCP_RACK_RECOVERY_THRESH (16)
 * no. of successful recoveries (accounts for full DSACK-based loss
 * recovery undo). After that, reset it to default (min_rtt/4).
 *
 * At max, reo_wnd is incremented only once per rtt. So that the new
 * DSACK on which we are reacting, is due to the spurious retx (approx)
 * after the reo_wnd has been updated last time.
 *
 * reo_wnd is tracked in terms of steps (of min_rtt/4), rather than
 * absolute value to account for change in rtt.
 */
/*
 * 当某一轮收到一个D-SACK数据包，就将时间窗口增加一个min_rtt/4，
 * 当然时间窗口值不能超过当前srtt的值，最大可以增加到64min_rtt的时间窗口值。
 * 当连续十六轮都没有再收到过D-SACK数据包，就将时间窗口值重置为min_rtt/4
 */
void tcp_rack_update_reo_wnd(struct sock *sk, struct rate_sample *rs)
{
	struct tcp_sock *tp = tcp_sk(sk);

    /* TCP_RACK_STATIC_REO_WND为0x02，如果设置了该值，就回到旧版的静态时间窗口功能，默认是开启0x01 */
	if (sock_net(sk)->ipv4.sysctl_tcp_recovery & TCP_RACK_STATIC_REO_WND ||
	    !rs->prior_delivered)
		return;

	/* Disregard DSACK if a rtt has not passed since we adjusted reo_wnd */
	if (before(rs->prior_delivered, tp->rack.last_delivered))
		tp->rack.dsack_seen = 0;

	/* Adjust the reo_wnd if update is pending */
	if (tp->rack.dsack_seen) {
		tp->rack.reo_wnd_steps = min_t(u32, 0xFF,
					       tp->rack.reo_wnd_steps + 1); /* 将时间窗口增加一个min_rtt/4 */
		tp->rack.dsack_seen = 0;
		tp->rack.last_delivered = tp->delivered;
		tp->rack.reo_wnd_persist = TCP_RACK_RECOVERY_THRESH;/* 重置为16轮 */
	} else if (!tp->rack.reo_wnd_persist) {
        /* 连续16轮没再收到D-SACK信息，则认为网络乱序已经变好，将时间窗口值变小 */
		tp->rack.reo_wnd_steps = 1;
	}
}

/* RFC6582 NewReno recovery for non-SACK connection. It simply retransmits
 * the next unacked packet upon receiving
 * a) three or more DUPACKs to start the fast recovery
 * b) an ACK acknowledging new data during the fast recovery.
 */
void tcp_newreno_mark_lost(struct sock *sk, bool snd_una_advanced)
{
	const u8 state = inet_csk(sk)->icsk_ca_state;
	struct tcp_sock *tp = tcp_sk(sk);

	if ((state < TCP_CA_Recovery && tp->sacked_out >= tp->reordering) ||
	    (state == TCP_CA_Recovery && snd_una_advanced)) {
	    // 当拥塞状态小于TCP_CA_Recovery，并且SACK（对于Reno，sacked_out等于dupack数量）确认的报文数量大于等于乱序等级
		struct sk_buff *skb = tcp_rtx_queue_head(sk);
		u32 mss;

		if (TCP_SKB_CB(skb)->sacked & TCPCB_LOST)
			return;

		mss = tcp_skb_mss(skb);
		if (tcp_skb_pcount(skb) > 1 && skb->len > mss)
		    // 重传队列首报文长度大于MSS，执行分片处理，仅标记一个长度为MSS的报文为丢失状态
			tcp_fragment(sk, TCP_FRAG_IN_RTX_QUEUE, skb,
				     mss, mss, GFP_ATOMIC);

		tcp_skb_mark_lost_uncond_verify(tp, skb);
	}
}
