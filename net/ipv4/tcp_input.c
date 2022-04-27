// SPDX-License-Identifier: GPL-2.0
/*
 * INET		An implementation of the TCP/IP protocol suite for the LINUX
 *		operating system.  INET is implemented using the  BSD Socket
 *		interface as the means of communication with the user level.
 *
 *		Implementation of the Transmission Control Protocol(TCP).
 *
 * Authors:	Ross Biro
 *		Fred N. van Kempen, <waltje@uWalt.NL.Mugnet.ORG>
 *		Mark Evans, <evansmp@uhura.aston.ac.uk>
 *		Corey Minyard <wf-rch!minyard@relay.EU.net>
 *		Florian La Roche, <flla@stud.uni-sb.de>
 *		Charles Hedrick, <hedrick@klinzhai.rutgers.edu>
 *		Linus Torvalds, <torvalds@cs.helsinki.fi>
 *		Alan Cox, <gw4pts@gw4pts.ampr.org>
 *		Matthew Dillon, <dillon@apollo.west.oic.com>
 *		Arnt Gulbrandsen, <agulbra@nvg.unit.no>
 *		Jorge Cwik, <jorge@laser.satlink.net>
 */

/*
 * Changes:
 *		Pedro Roque	:	Fast Retransmit/Recovery.
 *					Two receive queues.
 *					Retransmit queue handled by TCP.
 *					Better retransmit timer handling.
 *					New congestion avoidance.
 *					Header prediction.
 *					Variable renaming.
 *
 *		Eric		:	Fast Retransmit.
 *		Randy Scott	:	MSS option defines.
 *		Eric Schenk	:	Fixes to slow start algorithm.
 *		Eric Schenk	:	Yet another double ACK bug.
 *		Eric Schenk	:	Delayed ACK bug fixes.
 *		Eric Schenk	:	Floyd style fast retrans war avoidance.
 *		David S. Miller	:	Don't allow zero congestion window.
 *		Eric Schenk	:	Fix retransmitter so that it sends
 *					next packet on ack of previous packet.
 *		Andi Kleen	:	Moved open_request checking here
 *					and process RSTs for open_requests.
 *		Andi Kleen	:	Better prune_queue, and other fixes.
 *		Andrey Savochkin:	Fix RTT measurements in the presence of
 *					timestamps.
 *		Andrey Savochkin:	Check sequence numbers correctly when
 *					removing SACKs due to in sequence incoming
 *					data segments.
 *		Andi Kleen:		Make sure we never ack data there is not
 *					enough room for. Also make this condition
 *					a fatal error if it might still happen.
 *		Andi Kleen:		Add tcp_measure_rcv_mss to make
 *					connections with MSS<min(MTU,ann. MSS)
 *					work without delayed acks.
 *		Andi Kleen:		Process packets with PSH set in the
 *					fast path.
 *		J Hadi Salim:		ECN support
 *	 	Andrei Gurtov,
 *		Pasi Sarolahti,
 *		Panu Kuhlberg:		Experimental audit of TCP (re)transmission
 *					engine. Lots of bugs are found.
 *		Pasi Sarolahti:		F-RTO for dealing with spurious RTOs
 */

#define pr_fmt(fmt) "TCP: " fmt

#include <linux/mm.h>
#include <linux/slab.h>
#include <linux/module.h>
#include <linux/sysctl.h>
#include <linux/kernel.h>
#include <linux/prefetch.h>
#include <net/dst.h>
#include <net/tcp.h>
#include <net/inet_common.h>
#include <linux/ipsec.h>
#include <asm/unaligned.h>
#include <linux/errqueue.h>
#include <trace/events/tcp.h>
#include <linux/jump_label_ratelimit.h>
#include <net/busy_poll.h>
#include <net/mptcp.h>

int sysctl_tcp_max_orphans __read_mostly = NR_FILE;

#define FLAG_DATA		0x01 /* Incoming frame contained data.		*/ // 来了一个包含数据的包
#define FLAG_WIN_UPDATE		0x02 /* Incoming ACK was a window update.	*/ // 来了一个ACK用于更新窗口
#define FLAG_DATA_ACKED		0x04 /* This ACK acknowledged new data.		*/ // 对于数据的确认
// 对于重传数据的确认
#define FLAG_RETRANS_DATA_ACKED	0x08 /* "" "" some of which was retransmitted.	*/
#define FLAG_SYN_ACKED		0x10 /* This ACK acknowledged SYN.		*/ // 对于SYN的确认
#define FLAG_DATA_SACKED	0x20 /* New SACK.				*/ // 对于SYN的确认
#define FLAG_ECE		0x40 /* ECE in this ACK				*/ // 确认中旅带有ECE信息
#define FLAG_LOST_RETRANS	0x80 /* This ACK marks some retransmission lost */
// slowpath，需要做一些检查
#define FLAG_SLOWPATH		0x100 /* Do not skip RFC checks for window update.*/
#define FLAG_ORIG_SACK_ACKED	0x200 /* Never retransmitted data are (s)acked	*/
#define FLAG_SND_UNA_ADVANCED	0x400 /* Snd_una was changed (!= FLAG_DATA_ACKED) */
#define FLAG_DSACKING_ACK	0x800 /* SACK blocks contained D-SACK info */
#define FLAG_SET_XMIT_TIMER	0x1000 /* Set TLP or RTO timer */
// snd_una移动到一个sack中的一个位置
#define FLAG_SACK_RENEGING	0x2000 /* snd_una advanced to a sacked seq */
#define FLAG_UPDATE_TS_RECENT	0x4000 /* tcp_replace_ts_recent()  更新当前的时间戳 */
#define FLAG_NO_CHALLENGE_ACK	0x8000 /* do not call tcp_send_challenge_ack()	*/
#define FLAG_ACK_MAYBE_DELAYED	0x10000 /* Likely a delayed ACK */

#define FLAG_ACKED		(FLAG_DATA_ACKED|FLAG_SYN_ACKED) // 表示数据确认或者SYN确认
#define FLAG_NOT_DUP		(FLAG_DATA|FLAG_WIN_UPDATE|FLAG_ACKED) // 表示ACK是不重复的
// 表示是否在进入拥塞状态的时候被alert(原因可能是SACK丢包或者路由器提示拥塞)
#define FLAG_CA_ALERT		(FLAG_DATA_SACKED|FLAG_ECE|FLAG_DSACKING_ACK)
#define FLAG_FORWARD_PROGRESS	(FLAG_ACKED|FLAG_DATA_SACKED)

#define TCP_REMNANT (TCP_FLAG_FIN|TCP_FLAG_URG|TCP_FLAG_SYN|TCP_FLAG_PSH)
#define TCP_HP_BITS (~(TCP_RESERVED_BITS|TCP_FLAG_PSH))

#define REXMIT_NONE	0 /* no loss recovery to do */
#define REXMIT_LOST	1 /* retransmit packets marked lost */
#define REXMIT_NEW	2 /* FRTO-style transmit of unsent/new packets */

#if IS_ENABLED(CONFIG_TLS_DEVICE)
static DEFINE_STATIC_KEY_DEFERRED_FALSE(clean_acked_data_enabled, HZ);

void clean_acked_data_enable(struct inet_connection_sock *icsk,
			     void (*cad)(struct sock *sk, u32 ack_seq))
{
	icsk->icsk_clean_acked = cad;
	static_branch_deferred_inc(&clean_acked_data_enabled);
}
EXPORT_SYMBOL_GPL(clean_acked_data_enable);

void clean_acked_data_disable(struct inet_connection_sock *icsk)
{
	static_branch_slow_dec_deferred(&clean_acked_data_enabled);
	icsk->icsk_clean_acked = NULL;
}
EXPORT_SYMBOL_GPL(clean_acked_data_disable);

void clean_acked_data_flush(void)
{
	static_key_deferred_flush(&clean_acked_data_enabled);
}
EXPORT_SYMBOL_GPL(clean_acked_data_flush);
#endif

static void tcp_gro_dev_warn(struct sock *sk, const struct sk_buff *skb,
			     unsigned int len)
{
	static bool __once __read_mostly;

	if (!__once) {
		struct net_device *dev;

		__once = true;

		rcu_read_lock();
		dev = dev_get_by_index_rcu(sock_net(sk), skb->skb_iif);
		if (!dev || len >= dev->mtu)
			pr_warn("%s: Driver has suspect GRO implementation, TCP performance may be compromised.\n",
				dev ? dev->name : "Unknown driver");
		rcu_read_unlock();
	}
}

/* Adapt the MSS value used to make delayed ack decision to the
 * real world.
 */
static void tcp_measure_rcv_mss(struct sock *sk, const struct sk_buff *skb)
{
	struct inet_connection_sock *icsk = inet_csk(sk);
	const unsigned int lss = icsk->icsk_ack.last_seg_size;
	unsigned int len;

	icsk->icsk_ack.last_seg_size = 0;

	/* skb->len may jitter because of SACKs, even if peer
	 * sends good full-sized frames.
	 */
	len = skb_shinfo(skb)->gso_size ? : skb->len;
	if (len >= icsk->icsk_ack.rcv_mss) {
		icsk->icsk_ack.rcv_mss = min_t(unsigned int, len,
					       tcp_sk(sk)->advmss);
		/* Account for possibly-removed options */
		if (unlikely(len > icsk->icsk_ack.rcv_mss +
				   MAX_TCP_OPTION_SPACE))
			tcp_gro_dev_warn(sk, skb, len);
	} else {
		/* Otherwise, we make more careful check taking into account,
		 * that SACKs block is variable.
		 *
		 * "len" is invariant segment length, including TCP header.
		 */
		len += skb->data - skb_transport_header(skb);
		if (len >= TCP_MSS_DEFAULT + sizeof(struct tcphdr) ||
		    /* If PSH is not set, packet should be
		     * full sized, provided peer TCP is not badly broken.
		     * This observation (if it is correct 8)) allows
		     * to handle super-low mtu links fairly.
		     */
		    (len >= TCP_MIN_MSS + sizeof(struct tcphdr) &&
		     !(tcp_flag_word(tcp_hdr(skb)) & TCP_REMNANT))) {
			/* Subtract also invariant (if peer is RFC compliant),
			 * tcp header plus fixed timestamp option length.
			 * Resulting "len" is MSS free of SACK jitter.
			 */
			len -= tcp_sk(sk)->tcp_header_len;
			icsk->icsk_ack.last_seg_size = len;
			if (len == lss) {
				icsk->icsk_ack.rcv_mss = len;
				return;
			}
		}
        // 收到第一个小于mss的skb，标记ICSK_ACK_PUSHED
        // 收到第二个时，标记为ICSK_ACK_PUSHED2
        // 然后在tcp_cleanup_rbuf里判断为ICSK_ACK_PUSHED2就回复ack
		if (icsk->icsk_ack.pending & ICSK_ACK_PUSHED)
			icsk->icsk_ack.pending |= ICSK_ACK_PUSHED2;
		icsk->icsk_ack.pending |= ICSK_ACK_PUSHED;
	}
}

static void tcp_incr_quickack(struct sock *sk, unsigned int max_quickacks)
{
	struct inet_connection_sock *icsk = inet_csk(sk);
	unsigned int quickacks = tcp_sk(sk)->rcv_wnd / (2 * icsk->icsk_ack.rcv_mss);

	if (quickacks == 0)
		quickacks = 2;
	quickacks = min(quickacks, max_quickacks);
	if (quickacks > icsk->icsk_ack.quick)
		icsk->icsk_ack.quick = quickacks;
}

void tcp_enter_quickack_mode(struct sock *sk, unsigned int max_quickacks)
{
	struct inet_connection_sock *icsk = inet_csk(sk);

	tcp_incr_quickack(sk, max_quickacks);
	inet_csk_exit_pingpong_mode(sk);
	icsk->icsk_ack.ato = TCP_ATO_MIN;
}
EXPORT_SYMBOL(tcp_enter_quickack_mode);

/* Send ACKs quickly, if "quick" count is not exhausted
 * and the session is not interactive.
 */

static bool tcp_in_quickack_mode(struct sock *sk)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);
	const struct dst_entry *dst = __sk_dst_get(sk);

	return (dst && dst_metric(dst, RTAX_QUICKACK)) ||
		(icsk->icsk_ack.quick && !inet_csk_in_pingpong_mode(sk));
}

static void tcp_ecn_queue_cwr(struct tcp_sock *tp)
{
	if (tp->ecn_flags & TCP_ECN_OK)
		tp->ecn_flags |= TCP_ECN_QUEUE_CWR;
}

static void tcp_ecn_accept_cwr(struct sock *sk, const struct sk_buff *skb)
{
	if (tcp_hdr(skb)->cwr) {
		tcp_sk(sk)->ecn_flags &= ~TCP_ECN_DEMAND_CWR;

		/* If the sender is telling us it has entered CWR, then its
		 * cwnd may be very low (even just 1 packet), so we should ACK
		 * immediately.
		 */
		if (TCP_SKB_CB(skb)->seq != TCP_SKB_CB(skb)->end_seq)
			inet_csk(sk)->icsk_ack.pending |= ICSK_ACK_NOW;
	}
}

static void tcp_ecn_withdraw_cwr(struct tcp_sock *tp)
{
	tp->ecn_flags &= ~TCP_ECN_QUEUE_CWR;
}

static void __tcp_ecn_check_ce(struct sock *sk, const struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);

	switch (TCP_SKB_CB(skb)->ip_dsfield & INET_ECN_MASK) {
	case INET_ECN_NOT_ECT:
		/* Funny extension: if ECT is not set on a segment,
		 * and we already seen ECT on a previous segment,
		 * it is probably a retransmit.
		 */
		if (tp->ecn_flags & TCP_ECN_SEEN)
			tcp_enter_quickack_mode(sk, 2);
		break;
	case INET_ECN_CE:
		if (tcp_ca_needs_ecn(sk))
			tcp_ca_event(sk, CA_EVENT_ECN_IS_CE);

		if (!(tp->ecn_flags & TCP_ECN_DEMAND_CWR)) {
			/* Better not delay acks, sender can have a very low cwnd */
			tcp_enter_quickack_mode(sk, 2);
			tp->ecn_flags |= TCP_ECN_DEMAND_CWR;
		}
		tp->ecn_flags |= TCP_ECN_SEEN;
		break;
	default:
		if (tcp_ca_needs_ecn(sk))
			tcp_ca_event(sk, CA_EVENT_ECN_NO_CE);
		tp->ecn_flags |= TCP_ECN_SEEN;
		break;
	}
}

static void tcp_ecn_check_ce(struct sock *sk, const struct sk_buff *skb)
{
	if (tcp_sk(sk)->ecn_flags & TCP_ECN_OK)
		__tcp_ecn_check_ce(sk, skb);
}

static void tcp_ecn_rcv_synack(struct tcp_sock *tp, const struct tcphdr *th)
{
	if ((tp->ecn_flags & TCP_ECN_OK) && (!th->ece || th->cwr))
		tp->ecn_flags &= ~TCP_ECN_OK;
}

static void tcp_ecn_rcv_syn(struct tcp_sock *tp, const struct tcphdr *th)
{
	if ((tp->ecn_flags & TCP_ECN_OK) && (!th->ece || !th->cwr))
		tp->ecn_flags &= ~TCP_ECN_OK;
}

static bool tcp_ecn_rcv_ecn_echo(const struct tcp_sock *tp, const struct tcphdr *th)
{
	if (th->ece && !th->syn && (tp->ecn_flags & TCP_ECN_OK))
		return true;
	return false;
}

/* Buffer size and advertised window tuning.
 *
 * 1. Tuning sk->sk_sndbuf, when connection enters established state.
 */

static void tcp_sndbuf_expand(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	const struct tcp_congestion_ops *ca_ops = inet_csk(sk)->icsk_ca_ops;
	int sndmem, per_mss;
	u32 nr_segs;

	/* Worst case is non GSO/TSO : each frame consumes one skb
	 * and skb->head is kmalloced using power of two area of memory
	 */
	per_mss = max_t(u32, tp->rx_opt.mss_clamp, tp->mss_cache) +
		  MAX_TCP_HEADER +
		  SKB_DATA_ALIGN(sizeof(struct skb_shared_info));

	per_mss = roundup_pow_of_two(per_mss) +
		  SKB_DATA_ALIGN(sizeof(struct sk_buff));

	nr_segs = max_t(u32, TCP_INIT_CWND, tp->snd_cwnd);
	nr_segs = max_t(u32, nr_segs, tp->reordering + 1);

	/* Fast Recovery (RFC 5681 3.2) :
	 * Cubic needs 1.7 factor, rounded to 2 to include
	 * extra cushion (application might react slowly to EPOLLOUT)
	 */
	sndmem = ca_ops->sndbuf_expand ? ca_ops->sndbuf_expand(sk) : 2;
	sndmem *= nr_segs * per_mss;

	if (sk->sk_sndbuf < sndmem)
		WRITE_ONCE(sk->sk_sndbuf,
			   min(sndmem, sock_net(sk)->ipv4.sysctl_tcp_wmem[2]));
}

/* 2. Tuning advertised window (window_clamp, rcv_ssthresh)
 *
 * All tcp_full_space() is split to two parts: "network" buffer, allocated
 * forward and advertised in receiver window (tp->rcv_wnd) and
 * "application buffer", required to isolate scheduling/application
 * latencies from network.
 * window_clamp is maximal advertised window. It can be less than
 * tcp_full_space(), in this case tcp_full_space() - window_clamp
 * is reserved for "application" buffer. The less window_clamp is
 * the smoother our behaviour from viewpoint of network, but the lower
 * throughput and the higher sensitivity of the connection to losses. 8)
 *
 * rcv_ssthresh is more strict window_clamp used at "slow start"
 * phase to predict further behaviour of this connection.
 * It is used for two goals:
 * - to enforce header prediction at sender, even when application
 *   requires some significant "application buffer". It is check #1.
 * - to prevent pruning of receive queue because of misprediction
 *   of receiver window. Check #2.
 *
 * The scheme does not work when sender sends good segments opening
 * window and then starts to feed us spaghetti. But it should work
 * in common situations. Otherwise, we have to rely on queue collapsing.
 */

/* Slow part of check#2. */
static int __tcp_grow_window(const struct sock *sk, const struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	/* Optimize this! */
	int truesize = tcp_win_from_space(sk, skb->truesize) >> 1;
	int window = tcp_win_from_space(sk, sock_net(sk)->ipv4.sysctl_tcp_rmem[2]) >> 1;

	while (tp->rcv_ssthresh <= window) {
		if (truesize <= skb->len)
			return 2 * inet_csk(sk)->icsk_ack.rcv_mss;

		truesize >>= 1;
		window >>= 1;
	}
	return 0;
}

static void tcp_grow_window(struct sock *sk, const struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	int room;

	room = min_t(int, tp->window_clamp, tcp_space(sk)) - tp->rcv_ssthresh;

	/* Check #1 */
	if (room > 0 && !tcp_under_memory_pressure(sk)) {
		int incr;

		/* Check #2. Increase window, if skb with such overhead
		 * will fit to rcvbuf in future.
		 */
		if (tcp_win_from_space(sk, skb->truesize) <= skb->len)
			incr = 2 * tp->advmss;
		else
			incr = __tcp_grow_window(sk, skb);

		if (incr) {
			incr = max_t(int, incr, 2 * skb->len);
			tp->rcv_ssthresh += min(room, incr);
			inet_csk(sk)->icsk_ack.quick |= 1;
		}
	}
}

/* 3. Try to fixup all. It is made immediately after connection enters
 *    established state.
 */
static void tcp_init_buffer_space(struct sock *sk)
{
	int tcp_app_win = sock_net(sk)->ipv4.sysctl_tcp_app_win;
	struct tcp_sock *tp = tcp_sk(sk);
	int maxwin;

	if (!(sk->sk_userlocks & SOCK_SNDBUF_LOCK))
		tcp_sndbuf_expand(sk);

	tp->rcvq_space.space = min_t(u32, tp->rcv_wnd, TCP_INIT_CWND * tp->advmss);
	tcp_mstamp_refresh(tp);
	tp->rcvq_space.time = tp->tcp_mstamp;
	tp->rcvq_space.seq = tp->copied_seq;

	maxwin = tcp_full_space(sk);

	if (tp->window_clamp >= maxwin) {
		tp->window_clamp = maxwin;

		if (tcp_app_win && maxwin > 4 * tp->advmss)
			tp->window_clamp = max(maxwin -
					       (maxwin >> tcp_app_win),
					       4 * tp->advmss);
	}

	/* Force reservation of one segment. */
	if (tcp_app_win &&
	    tp->window_clamp > 2 * tp->advmss &&
	    tp->window_clamp + tp->advmss > maxwin)
		tp->window_clamp = max(2 * tp->advmss, maxwin - tp->advmss);

	tp->rcv_ssthresh = min(tp->rcv_ssthresh, tp->window_clamp);
	tp->snd_cwnd_stamp = tcp_jiffies32;
}

/* 4. Recalculate window clamp after socket hit its memory bounds. */
static void tcp_clamp_window(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct inet_connection_sock *icsk = inet_csk(sk);
	struct net *net = sock_net(sk);

	icsk->icsk_ack.quick = 0;

	if (sk->sk_rcvbuf < net->ipv4.sysctl_tcp_rmem[2] &&
	    !(sk->sk_userlocks & SOCK_RCVBUF_LOCK) &&
	    !tcp_under_memory_pressure(sk) &&
	    sk_memory_allocated(sk) < sk_prot_mem_limits(sk, 0)) {
		WRITE_ONCE(sk->sk_rcvbuf,
			   min(atomic_read(&sk->sk_rmem_alloc),
			       net->ipv4.sysctl_tcp_rmem[2]));
	}
	if (atomic_read(&sk->sk_rmem_alloc) > sk->sk_rcvbuf)
		tp->rcv_ssthresh = min(tp->window_clamp, 2U * tp->advmss);
}

/* Initialize RCV_MSS value.
 * RCV_MSS is an our guess about MSS used by the peer.
 * We haven't any direct information about the MSS.
 * It's better to underestimate the RCV_MSS rather than overestimate.
 * Overestimations make us ACKing less frequently than needed.
 * Underestimations are more easy to detect and fix by tcp_measure_rcv_mss().
 */
void tcp_initialize_rcv_mss(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	unsigned int hint = min_t(unsigned int, tp->advmss, tp->mss_cache);

	hint = min(hint, tp->rcv_wnd / 2);
	hint = min(hint, TCP_MSS_DEFAULT);
	hint = max(hint, TCP_MIN_MSS);

	inet_csk(sk)->icsk_ack.rcv_mss = hint;
}
EXPORT_SYMBOL(tcp_initialize_rcv_mss);

/* Receiver "autotuning" code.
 *
 * The algorithm for RTT estimation w/o timestamps is based on
 * Dynamic Right-Sizing (DRS) by Wu Feng and Mike Fisk of LANL.
 * <http://public.lanl.gov/radiant/pubs.html#DRS>
 *
 * More detail on this code can be found at
 * <http://staff.psc.edu/jheffner/>,
 * though this reference is out of date.  A new paper
 * is pending.
 */
static void tcp_rcv_rtt_update(struct tcp_sock *tp, u32 sample, int win_dep)
{
	u32 new_sample = tp->rcv_rtt_est.rtt_us;
	long m = sample;

	if (new_sample != 0) {
		/* If we sample in larger samples in the non-timestamp
		 * case, we could grossly overestimate the RTT especially
		 * with chatty applications or bulk transfer apps which
		 * are stalled on filesystem I/O.
		 *
		 * Also, since we are only going for a minimum in the
		 * non-timestamp case, we do not smooth things out
		 * else with timestamps disabled convergence takes too
		 * long.
		 */
		if (!win_dep) {
			m -= (new_sample >> 3);
			new_sample += m;
		} else {
			m <<= 3;
			if (m < new_sample)
				new_sample = m;
		}
	} else {
		/* No previous measure. */
		new_sample = m << 3;
	}

	tp->rcv_rtt_est.rtt_us = new_sample;
}

static inline void tcp_rcv_rtt_measure(struct tcp_sock *tp)
{
	u32 delta_us;

	if (tp->rcv_rtt_est.time == 0)
		goto new_measure;
	if (before(tp->rcv_nxt, tp->rcv_rtt_est.seq))
		return;
	delta_us = tcp_stamp_us_delta(tp->tcp_mstamp, tp->rcv_rtt_est.time);
	if (!delta_us)
		delta_us = 1;
	tcp_rcv_rtt_update(tp, delta_us, 1);

new_measure:
	tp->rcv_rtt_est.seq = tp->rcv_nxt + tp->rcv_wnd;
	tp->rcv_rtt_est.time = tp->tcp_mstamp;
}

static inline void tcp_rcv_rtt_measure_ts(struct sock *sk,
					  const struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (tp->rx_opt.rcv_tsecr == tp->rcv_rtt_last_tsecr)
		return;
	tp->rcv_rtt_last_tsecr = tp->rx_opt.rcv_tsecr;

	if (TCP_SKB_CB(skb)->end_seq -
	    TCP_SKB_CB(skb)->seq >= inet_csk(sk)->icsk_ack.rcv_mss) {
		u32 delta = tcp_time_stamp(tp) - tp->rx_opt.rcv_tsecr;
		u32 delta_us;

		if (likely(delta < INT_MAX / (USEC_PER_SEC / TCP_TS_HZ))) {
			if (!delta)
				delta = 1;
			delta_us = delta * (USEC_PER_SEC / TCP_TS_HZ);
			tcp_rcv_rtt_update(tp, delta_us, 0);
		}
	}
}

/*
 * This function should be called every time data is copied to user space.
 * It calculates the appropriate TCP receive buffer space.
 */
void tcp_rcv_space_adjust(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 copied;
	int time;

	trace_tcp_rcv_space_adjust(sk);

	tcp_mstamp_refresh(tp);
	time = tcp_stamp_us_delta(tp->tcp_mstamp, tp->rcvq_space.time);
	if (time < (tp->rcv_rtt_est.rtt_us >> 3) || tp->rcv_rtt_est.rtt_us == 0)
		return;

	/* Number of bytes copied to user in last RTT */
	copied = tp->copied_seq - tp->rcvq_space.seq;
	if (copied <= tp->rcvq_space.space)
		goto new_measure;

	/* A bit of theory :
	 * copied = bytes received in previous RTT, our base window
	 * To cope with packet losses, we need a 2x factor
	 * To cope with slow start, and sender growing its cwin by 100 %
	 * every RTT, we need a 4x factor, because the ACK we are sending
	 * now is for the next RTT, not the current one :
	 * <prev RTT . ><current RTT .. ><next RTT .... >
	 */

	if (sock_net(sk)->ipv4.sysctl_tcp_moderate_rcvbuf &&
	    !(sk->sk_userlocks & SOCK_RCVBUF_LOCK)) {
		int rcvmem, rcvbuf;
		u64 rcvwin, grow;

		/* minimal window to cope with packet losses, assuming
		 * steady state. Add some cushion because of small variations.
		 */
		rcvwin = ((u64)copied << 1) + 16 * tp->advmss;

		/* Accommodate for sender rate increase (eg. slow start) */
		grow = rcvwin * (copied - tp->rcvq_space.space);
		do_div(grow, tp->rcvq_space.space);
		rcvwin += (grow << 1);

		rcvmem = SKB_TRUESIZE(tp->advmss + MAX_TCP_HEADER);
		while (tcp_win_from_space(sk, rcvmem) < tp->advmss)
			rcvmem += 128;

		do_div(rcvwin, tp->advmss);
		rcvbuf = min_t(u64, rcvwin * rcvmem,
			       sock_net(sk)->ipv4.sysctl_tcp_rmem[2]);
		if (rcvbuf > sk->sk_rcvbuf) {
			WRITE_ONCE(sk->sk_rcvbuf, rcvbuf);

			/* Make the window clamp follow along.  */
			tp->window_clamp = tcp_win_from_space(sk, rcvbuf);
		}
	}
	tp->rcvq_space.space = copied;

new_measure:
	tp->rcvq_space.seq = tp->copied_seq;
	tp->rcvq_space.time = tp->tcp_mstamp;
}

/* There is something which you must keep in mind when you analyze the
 * behavior of the tp->ato delayed ack timeout interval.  When a
 * connection starts up, we want to ack as quickly as possible.  The
 * problem is that "good" TCP's do slow start at the beginning of data
 * transmission.  The means that until we send the first few ACK's the
 * sender will sit on his end and only queue most of his data, because
 * he can only send snd_cwnd unacked packets at any given time.  For
 * each ACK we send, he increments snd_cwnd and transmits more of his
 * queue.  -DaveM
 */
static void tcp_event_data_recv(struct sock *sk, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct inet_connection_sock *icsk = inet_csk(sk);
	u32 now;

    /* 接收到了数据，设置ACK需调度标志 */
	inet_csk_schedule_ack(sk);

	tcp_measure_rcv_mss(sk, skb);

	tcp_rcv_rtt_measure(tp);

	now = tcp_jiffies32;

    /* 以下为根据接收间隔更新icsk_ack.ato，该值主要用于判断pingpong模式见函数 tcp_event_data_sent */
	if (!icsk->icsk_ack.ato) {
		/* The _first_ data packet received, initialize
		 * delayed ACK engine.
		 */
		tcp_incr_quickack(sk, TCP_MAX_QUICKACKS);
		icsk->icsk_ack.ato = TCP_ATO_MIN;
	} else {
		int m = now - icsk->icsk_ack.lrcvtime;

		if (m <= TCP_ATO_MIN / 2) {
			/* The fastest case is the first. */
			icsk->icsk_ack.ato = (icsk->icsk_ack.ato >> 1) + TCP_ATO_MIN / 2;
		} else if (m < icsk->icsk_ack.ato) {
			icsk->icsk_ack.ato = (icsk->icsk_ack.ato >> 1) + m;
			if (icsk->icsk_ack.ato > icsk->icsk_rto)
				icsk->icsk_ack.ato = icsk->icsk_rto;
		} else if (m > icsk->icsk_rto) {
			/* Too long gap. Apparently sender failed to
			 * restart window, so that we send ACKs quickly.
			 */
			tcp_incr_quickack(sk, TCP_MAX_QUICKACKS);
			sk_mem_reclaim(sk);
		}
	}
	icsk->icsk_ack.lrcvtime = now;

	tcp_ecn_check_ce(sk, skb);

    /* 每次接收到来自对方的一个TCP数据报，且数据报长度大于128字节时，
     * 我们需要调用tcp_grow_window，增加rcv_ssthresh的值，一般每次为rcv_ssthresh增长两倍的mss，
     * 增加的条件是rcv_ssthresh小于window_clamp,并且 rcv_ssthresh小于接收缓存剩余空间的3/4，
     * 同时tcp_memory_pressure没有被置位(即接收缓存中的数据量没有太大)。
     * tcp_grow_window中对新收到的skb的长度还有一些限制，并不总是增长rcv_ssthresh的值
     * rcv_ssthresh是当前的接收窗口大小的一个阀值，其初始值就置为rcv_wnd。它跟rcv_wnd配合工作，当本地socket收到数据报，并满足一定条件时，增长rcv_ssthresh的值，在下一次发送数据报组建TCP首部时，需要通告对方当前的接收窗口大小，这时需要更新rcv_wnd，此时rcv_wnd的取值不能超过rcv_ssthresh的值。两者配合，达到一个滑动窗口大小缓慢增长的效果。
     */
	if (skb->len >= 128)
		tcp_grow_window(sk, skb);
}

/* Called to compute a smoothed rtt estimate. The data fed to this
 * routine either comes from timestamps, or from segments that were
 * known _not_ to have been retransmitted [see Karn/Partridge
 * Proceedings SIGCOMM 87]. The algorithm is from the SIGCOMM 88
 * piece by Van Jacobson.
 * NOTE: the next three routines used to be one big routine.
 * To save cycles in the RFC 1323 implementation it was better to break
 * it up into three procedures. -- erics
 */
static void tcp_rtt_estimator(struct sock *sk, long mrtt_us)
{
	struct tcp_sock *tp = tcp_sk(sk);
	long m = mrtt_us; /* RTT */
	u32 srtt = tp->srtt_us;

	/*	The following amusing code comes from Jacobson's
	 *	article in SIGCOMM '88.  Note that rtt and mdev
	 *	are scaled versions of rtt and mean deviation.
	 *	This is designed to be as fast as possible
	 *	m stands for "measurement".
	 *
	 *	On a 1990 paper the rto value is changed to:
	 *	RTO = rtt + 4 * mdev
	 *
	 * Funny. This algorithm seems to be very broken.
	 * These formulae increase RTO, when it should be decreased, increase
	 * too slowly, when it should be increased quickly, decrease too quickly
	 * etc. I guess in BSD RTO takes ONE value, so that it is absolutely
	 * does not matter how to _calculate_ it. Seems, it was trap
	 * that VJ failed to avoid. 8)
	 */
	if (srtt != 0) {
		m -= (srtt >> 3);	/* m is now error in rtt est */
		srtt += m;		/* rtt = 7/8 rtt + 1/8 new */
		if (m < 0) {
			m = -m;		/* m is now abs(error) */
			m -= (tp->mdev_us >> 2);   /* similar update on mdev */
			/* This is similar to one of Eifel findings.
			 * Eifel blocks mdev updates when rtt decreases.
			 * This solution is a bit different: we use finer gain
			 * for mdev in this case (alpha*beta).
			 * Like Eifel it also prevents growth of rto,
			 * but also it limits too fast rto decreases,
			 * happening in pure Eifel.
			 */
			if (m > 0)
				m >>= 3;
		} else {
			m -= (tp->mdev_us >> 2);   /* similar update on mdev */
		}
		tp->mdev_us += m;		/* mdev = 3/4 mdev + 1/4 new */
		if (tp->mdev_us > tp->mdev_max_us) {
			tp->mdev_max_us = tp->mdev_us;
			if (tp->mdev_max_us > tp->rttvar_us)
				tp->rttvar_us = tp->mdev_max_us;
		}
		if (after(tp->snd_una, tp->rtt_seq)) {
			if (tp->mdev_max_us < tp->rttvar_us)
				tp->rttvar_us -= (tp->rttvar_us - tp->mdev_max_us) >> 2;
			tp->rtt_seq = tp->snd_nxt;
			tp->mdev_max_us = tcp_rto_min_us(sk);

			tcp_bpf_rtt(sk);
		}
	} else {
		/* no previous measure. */
		srtt = m << 3;		/* take the measured time to be rtt */
		tp->mdev_us = m << 1;	/* make sure rto = 3*rtt */
		tp->rttvar_us = max(tp->mdev_us, tcp_rto_min_us(sk));
		tp->mdev_max_us = tp->rttvar_us;
		tp->rtt_seq = tp->snd_nxt;

		tcp_bpf_rtt(sk);
	}
	tp->srtt_us = max(1U, srtt);
}

static void tcp_update_pacing_rate(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	u64 rate;

	/* set sk_pacing_rate to 200 % of current rate (mss * cwnd / srtt) */
	rate = (u64)tp->mss_cache * ((USEC_PER_SEC / 100) << 3);

	/* current rate is (cwnd * mss) / srtt
	 * In Slow Start [1], set sk_pacing_rate to 200 % the current rate.
	 * In Congestion Avoidance phase, set it to 120 % the current rate.
	 *
	 * [1] : Normal Slow Start condition is (tp->snd_cwnd < tp->snd_ssthresh)
	 *	 If snd_cwnd >= (tp->snd_ssthresh / 2), we are approaching
	 *	 end of slow start and should slow down.
	 */
	if (tp->snd_cwnd < tp->snd_ssthresh / 2)
		rate *= sock_net(sk)->ipv4.sysctl_tcp_pacing_ss_ratio;
	else
		rate *= sock_net(sk)->ipv4.sysctl_tcp_pacing_ca_ratio;

	rate *= max(tp->snd_cwnd, tp->packets_out);

	if (likely(tp->srtt_us))
		do_div(rate, tp->srtt_us);

	/* WRITE_ONCE() is needed because sch_fq fetches sk_pacing_rate
	 * without any lock. We want to make sure compiler wont store
	 * intermediate values in this location.
	 */
	WRITE_ONCE(sk->sk_pacing_rate, min_t(u64, rate,
					     sk->sk_max_pacing_rate));
}

/* Calculate rto without backoff.  This is the second half of Van Jacobson's
 * routine referred to above.
 */
static void tcp_set_rto(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	/* Old crap is replaced with new one. 8)
	 *
	 * More seriously:
	 * 1. If rtt variance happened to be less 50msec, it is hallucination.
	 *    It cannot be less due to utterly erratic ACK generation made
	 *    at least by solaris and freebsd. "Erratic ACKs" has _nothing_
	 *    to do with delayed acks, because at cwnd>2 true delack timeout
	 *    is invisible. Actually, Linux-2.4 also generates erratic
	 *    ACKs in some circumstances.
	 */
	inet_csk(sk)->icsk_rto = __tcp_set_rto(tp);

	/* 2. Fixups made earlier cannot be right.
	 *    If we do not estimate RTO correctly without them,
	 *    all the algo is pure shit and should be replaced
	 *    with correct one. It is exactly, which we pretend to do.
	 */

	/* NOTE: clamping at TCP_RTO_MIN is not required, current algo
	 * guarantees that rto is higher.
	 */
	tcp_bound_rto(sk);
}

__u32 tcp_init_cwnd(const struct tcp_sock *tp, const struct dst_entry *dst)
{
	__u32 cwnd = (dst ? dst_metric(dst, RTAX_INITCWND) : 0);

	if (!cwnd)
		cwnd = TCP_INIT_CWND;
	return min_t(__u32, cwnd, tp->snd_cwnd_clamp);
}

/* Take a notice that peer is sending D-SACKs */
static void tcp_dsack_seen(struct tcp_sock *tp)
{
	tp->rx_opt.sack_ok |= TCP_DSACK_SEEN;
	tp->rack.dsack_seen = 1;
	tp->dsack_dups++;
}

/* It's reordering when higher sequence was delivered (i.e. sacked) before
 * some lower never-retransmitted sequence ("low_seq"). The maximum reordering
 * distance is approximated in full-mss packet distance ("reordering").
 */
/*
 * 如果当前未确认序号low_seq（也未重传）不在最高的SACK确认序号之前，表明没有发生乱序，不调整reordering。
 * 否则，乱序度由最高SACK确认序号减去当前序号low_seq而得
 */
static void tcp_check_sack_reordering(struct sock *sk, const u32 low_seq,
				      const int ts)
{
	struct tcp_sock *tp = tcp_sk(sk);
	const u32 mss = tp->mss_cache;
	u32 fack, metric;

	fack = tcp_highest_sack_seq(tp);
	if (!before(low_seq, fack))
		return;

	metric = fack - low_seq;
	if ((metric > tp->reordering * mss) && mss) {
	    /*
	     * 套接口乱序级别reordering的单位为MSS，检查当前的乱序metric是否超出记录值，
	     * 如果为真，更新乱序级别reordering（MSS的整数倍），乱序级别不超过限定的最大值（tcp_max_reordering）
	     */
#if FASTRETRANS_DEBUG > 1
		pr_debug("Disorder%d %d %u f%u s%u rr%d\n",
			 tp->rx_opt.sack_ok, inet_csk(sk)->icsk_ca_state,
			 tp->reordering,
			 0,
			 tp->sacked_out,
			 tp->undo_marker ? tp->undo_retrans : 0);
#endif
		tp->reordering = min_t(u32, (metric + mss - 1) / mss,
				       sock_net(sk)->ipv4.sysctl_tcp_max_reordering);
	}

	/* This exciting event is worth to be remembered. 8) */
	tp->reord_seen++;
	NET_INC_STATS(sock_net(sk),
		      ts ? LINUX_MIB_TCPTSREORDER : LINUX_MIB_TCPSACKREORDER);
}

/* This must be called before lost_out is incremented */
static void tcp_verify_retransmit_hint(struct tcp_sock *tp, struct sk_buff *skb)
{
	if ((!tp->retransmit_skb_hint && tp->retrans_out >= tp->lost_out) ||
	    (tp->retransmit_skb_hint &&
	     before(TCP_SKB_CB(skb)->seq,
		    TCP_SKB_CB(tp->retransmit_skb_hint)->seq)))
		tp->retransmit_skb_hint = skb;
}

/* Sum the number of packets on the wire we have marked as lost.
 * There are two cases we care about here:
 * a) Packet hasn't been marked lost (nor retransmitted),
 *    and this is the first loss.
 * b) Packet has been marked both lost and retransmitted,
 *    and this means we think it was lost again.
 */
static void tcp_sum_lost(struct tcp_sock *tp, struct sk_buff *skb)
{
	__u8 sacked = TCP_SKB_CB(skb)->sacked;

	if (!(sacked & TCPCB_LOST) || // 报文没有被标记为丢失，第一次丢失
	    ((sacked & TCPCB_LOST) && (sacked & TCPCB_SACKED_RETRANS))) // 重传报文的再度丢失
		tp->lost += tcp_skb_pcount(skb); // 增加套接口报文丢失计数
		// 注意这里的lost通过包括重传丢失报文，而以上的lost_out计数不包括重传丢
}

static void tcp_skb_mark_lost(struct tcp_sock *tp, struct sk_buff *skb)
{
    // 报文没有被标记过丢失（TCPCB_LOST），也没有被SACK确认（TCPCB_SACKED_ACKED）
	if (!(TCP_SKB_CB(skb)->sacked & (TCPCB_LOST|TCPCB_SACKED_ACKED))) {
		tcp_verify_retransmit_hint(tp, skb); // 更新retransmit_skb_hint重传报文指针，其中记录的为首个应当重传的报文

        // 更新lost_out丢包统计
		tp->lost_out += tcp_skb_pcount(skb);
		tcp_sum_lost(tp, skb);
		TCP_SKB_CB(skb)->sacked |= TCPCB_LOST; // 设置TCPCB_LOST标志
	}
}

void tcp_skb_mark_lost_uncond_verify(struct tcp_sock *tp, struct sk_buff *skb)
{
    // 设置下一次重传时，应使用的重传报文skb（保存在retransmit_skb_hint）
	tcp_verify_retransmit_hint(tp, skb);

	tcp_sum_lost(tp, skb); // 更新套接口丢失报文计数
	if (!(TCP_SKB_CB(skb)->sacked & (TCPCB_LOST|TCPCB_SACKED_ACKED))) {// 报文没有设置过丢失标记TCPCB_LOST，并且也没有被SACK确认（对于Reno，无标志TCPCB_SACKED_ACKED）
		tp->lost_out += tcp_skb_pcount(skb);   // 增加丢失报文计数
		TCP_SKB_CB(skb)->sacked |= TCPCB_LOST; // 设置TCPCB_LOST标志位
	}
}

/* This procedure tags the retransmission queue when SACKs arrive.
 *
 * We have three tag bits: SACKED(S), RETRANS(R) and LOST(L).
 * Packets in queue with these bits set are counted in variables
 * sacked_out, retrans_out and lost_out, correspondingly.
 *
 * Valid combinations are:
 * Tag  InFlight	Description
 * 0	1		- orig segment is in flight.
 * S	0		- nothing flies, orig reached receiver.
 * L	0		- nothing flies, orig lost by net.
 * R	2		- both orig and retransmit are in flight.
 * L|R	1		- orig is lost, retransmit is in flight.
 * S|R  1		- orig reached receiver, retrans is still in flight.
 * (L|S|R is logically valid, it could occur when L|R is sacked,
 *  but it is equivalent to plain S and code short-curcuits it to S.
 *  L|S is logically invalid, it would mean -1 packet in flight 8))
 *
 * These 6 states form finite state machine, controlled by the following events:
 * 1. New ACK (+SACK) arrives. (tcp_sacktag_write_queue())
 * 2. Retransmission. (tcp_retransmit_skb(), tcp_xmit_retransmit_queue())
 * 3. Loss detection event of two flavors:
 *	A. Scoreboard estimator decided the packet is lost.
 *	   A'. Reno "three dupacks" marks head of queue lost.
 *	B. SACK arrives sacking SND.NXT at the moment, when the
 *	   segment was retransmitted.
 * 4. D-SACK added new rule: D-SACK changes any tag to S.
 *
 * It is pleasant to note, that state diagram turns out to be commutative,
 * so that we are allowed not to be bothered by order of our actions,
 * when multiple events arrive simultaneously. (see the function below).
 *
 * Reordering detection.
 * --------------------
 * Reordering metric is maximal distance, which a packet can be displaced
 * in packet stream. With SACKs we can estimate it:
 *
 * 1. SACK fills old hole and the corresponding segment was not
 *    ever retransmitted -> reordering. Alas, we cannot use it
 *    when segment was retransmitted.
 * 2. The last flaw is solved with D-SACK. D-SACK arrives
 *    for retransmitted and already SACKed segment -> reordering..
 * Both of these heuristics are not used in Loss state, when we cannot
 * account for retransmits accurately.
 *
 * SACK block validation.
 * ----------------------
 *
 * SACK block range validation checks that the received SACK block fits to
 * the expected sequence limits, i.e., it is between SND.UNA and SND.NXT.
 * Note that SND.UNA is not included to the range though being valid because
 * it means that the receiver is rather inconsistent with itself reporting
 * SACK reneging when it should advance SND.UNA. Such SACK block this is
 * perfectly valid, however, in light of RFC2018 which explicitly states
 * that "SACK block MUST reflect the newest segment.  Even if the newest
 * segment is going to be discarded ...", not that it looks very clever
 * in case of head skb. Due to potentional receiver driven attacks, we
 * choose to avoid immediate execution of a walk in write queue due to
 * reneging and defer head skb's loss recovery to standard loss recovery
 * procedure that will eventually trigger (nothing forbids us doing this).
 *
 * Implements also blockage to start_seq wrap-around. Problem lies in the
 * fact that though start_seq (s) is before end_seq (i.e., not reversed),
 * there's no guarantee that it will be before snd_nxt (n). The problem
 * happens when start_seq resides between end_seq wrap (e_w) and snd_nxt
 * wrap (s_w):
 *
 *         <- outs wnd ->                          <- wrapzone ->
 *         u     e      n                         u_w   e_w  s n_w
 *         |     |      |                          |     |   |  |
 * |<------------+------+----- TCP seqno space --------------+---------->|
 * ...-- <2^31 ->|                                           |<--------...
 * ...---- >2^31 ------>|                                    |<--------...
 *
 * Current code wouldn't be vulnerable but it's better still to discard such
 * crazy SACK blocks. Doing this check for start_seq alone closes somewhat
 * similar case (end_seq after snd_nxt wrap) as earlier reversed check in
 * snd_nxt wrap -> snd_una region will then become "well defined", i.e.,
 * equal to the ideal case (infinite seqno space without wrap caused issues).
 *
 * With D-SACK the lower bound is extended to cover sequence space below
 * SND.UNA down to undo_marker, which is the last point of interest. Yet
 * again, D-SACK block must not to go across snd_una (for the same reason as
 * for the normal SACK blocks, explained above). But there all simplicity
 * ends, TCP might receive valid D-SACKs below that. As long as they reside
 * fully below undo_marker they do not affect behavior in anyway and can
 * therefore be safely ignored. In rare cases (which are more or less
 * theoretical ones), the D-SACK will nicely cross that boundary due to skb
 * fragmentation and packet reordering past skb's retransmission. To consider
 * them correctly, the acceptable range must be extended even more though
 * the exact amount is rather hard to quantify. However, tp->max_window can
 * be used as an exaggerated estimate.
 */
static bool tcp_is_sackblock_valid(struct tcp_sock *tp, bool is_dsack,
				   u32 start_seq, u32 end_seq)
{
	/* Too far in future, or reversed (interpretation is ambiguous) */
	if (after(end_seq, tp->snd_nxt) || !before(start_seq, end_seq))
		return false;

	/* Nasty start_seq wrap-around check (see comments above) */
	if (!before(start_seq, tp->snd_nxt))
		return false;

	/* In outstanding window? ...This is valid exit for D-SACKs too.
	 * start_seq == snd_una is non-sensical (see comments above)
	 */
	if (after(start_seq, tp->snd_una))
		return true;

	if (!is_dsack || !tp->undo_marker)
		return false;

	/* ...Then it's D-SACK, and must reside below snd_una completely */
	if (after(end_seq, tp->snd_una))
		return false;

	if (!before(start_seq, tp->undo_marker))
		return true;

	/* Too old */
	if (!after(end_seq, tp->undo_marker))
		return false;

	/* Undo_marker boundary crossing (overestimates a lot). Known already:
	 *   start_seq < undo_marker and end_seq >= undo_marker.
	 */
	return !before(start_seq, end_seq - tp->max_window);
}

static bool tcp_check_dsack(struct sock *sk, const struct sk_buff *ack_skb,
			    struct tcp_sack_block_wire *sp, int num_sacks,
			    u32 prior_snd_una)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 start_seq_0 = get_unaligned_be32(&sp[0].start_seq);
	u32 end_seq_0 = get_unaligned_be32(&sp[0].end_seq);
	bool dup_sack = false;

	if (before(start_seq_0, TCP_SKB_CB(ack_skb)->ack_seq)) {
		dup_sack = true;
		tcp_dsack_seen(tp);
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPDSACKRECV);
	} else if (num_sacks > 1) {
		u32 end_seq_1 = get_unaligned_be32(&sp[1].end_seq);
		u32 start_seq_1 = get_unaligned_be32(&sp[1].start_seq);

		if (!after(end_seq_0, end_seq_1) &&
		    !before(start_seq_0, start_seq_1)) {
			dup_sack = true;
			tcp_dsack_seen(tp);
			NET_INC_STATS(sock_net(sk),
					LINUX_MIB_TCPDSACKOFORECV);
		}
	}

	/* D-SACK for already forgotten data... Do dumb counting. */
	if (dup_sack && tp->undo_marker && tp->undo_retrans > 0 &&
	    !after(end_seq_0, prior_snd_una) &&
	    after(end_seq_0, tp->undo_marker))
	    // SACK序号块被认定为DSACK，
	    // 并且undo_retrans大于零（进行过重传操作），
	    // 并且DSACK序号块的终止序号满足如下条件：(prior_SND.UNA >= end_seq_0 > undo_marker)
		tp->undo_retrans--; // undo_retrans递减一

	return dup_sack;
}

struct tcp_sacktag_state {
	u32	reord;
	/* Timestamps for earliest and latest never-retransmitted segment
	 * that was SACKed. RTO needs the earliest RTT to stay conservative,
	 * but congestion control should still get an accurate delay signal.
	 */
	u64	first_sackt;
	u64	last_sackt;
	struct rate_sample *rate;
	int	flag;
	unsigned int mss_now;
};

/* Check if skb is fully within the SACK block. In presence of GSO skbs,
 * the incoming SACK may not exactly match but we can find smaller MSS
 * aligned portion of it that matches. Therefore we might need to fragment
 * which may fail and creates some hassle (caller must handle error case
 * returns).
 *
 * FIXME: this could be merged to shift decision code
 */
static int tcp_match_skb_to_sack(struct sock *sk, struct sk_buff *skb,
				  u32 start_seq, u32 end_seq)
{
	int err;
	bool in_sack;
	unsigned int pkt_len;
	unsigned int mss;

	in_sack = !after(start_seq, TCP_SKB_CB(skb)->seq) &&
		  !before(end_seq, TCP_SKB_CB(skb)->end_seq);

	if (tcp_skb_pcount(skb) > 1 && !in_sack &&
	    after(TCP_SKB_CB(skb)->end_seq, start_seq)) {
		mss = tcp_skb_mss(skb);
		in_sack = !after(start_seq, TCP_SKB_CB(skb)->seq);

		if (!in_sack) {
			pkt_len = start_seq - TCP_SKB_CB(skb)->seq;
			if (pkt_len < mss)
				pkt_len = mss;
		} else {
			pkt_len = end_seq - TCP_SKB_CB(skb)->seq;
			if (pkt_len < mss)
				return -EINVAL;
		}

		/* Round if necessary so that SACKs cover only full MSSes
		 * and/or the remaining small portion (if present)
		 */
		if (pkt_len > mss) {
			unsigned int new_len = (pkt_len / mss) * mss;
			if (!in_sack && new_len < pkt_len)
				new_len += mss;
			pkt_len = new_len;
		}

		if (pkt_len >= skb->len && !in_sack)
			return 0;

		err = tcp_fragment(sk, TCP_FRAG_IN_RTX_QUEUE, skb,
				   pkt_len, mss, GFP_ATOMIC);
		if (err < 0)
			return err;
	}

	return in_sack;
}

/* Mark the given newly-SACKed range as such, adjusting counters and hints. */
static u8 tcp_sacktag_one(struct sock *sk,
			  struct tcp_sacktag_state *state, u8 sacked,
			  u32 start_seq, u32 end_seq,
			  int dup_sack, int pcount,
			  u64 xmit_time)
{
	struct tcp_sock *tp = tcp_sk(sk);

	/* Account D-SACK for retransmitted packet. */
    // 接收到D-SACK，并且报文被重传过（重传导致的DSACK，排除网络中错误的复制报文等情况）
	if (dup_sack && (sacked & TCPCB_RETRANS)) {
		if (tp->undo_marker && tp->undo_retrans > 0 &&
		    after(end_seq, tp->undo_marker))
            // SACK序号块被认定为DSACK，
            // 并且undo_retrans大于零（进行过重传操作），
            // 并且DSACK序号块的终止序号满足如下条件：(prior_SND.UNA >= end_seq_0 > undo_marker)
			tp->undo_retrans--;
		if ((sacked & TCPCB_SACKED_ACKED) &&
		    before(start_seq, state->reord)) // 报文的起始序号在reord之前，更新reord作为乱序的源头
				state->reord = start_seq;
	}

	/* Nothing to do; acked frame is about to be dropped (was ACKed). */
	if (!after(end_seq, tp->snd_una))
		return sacked;

	// 报文没有被重传过
	if (!(sacked & TCPCB_SACKED_ACKED)) {
		tcp_rack_advance(tp, sacked, end_seq, xmit_time);

		if (sacked & TCPCB_SACKED_RETRANS) {
			/* If the segment is not tagged as lost,
			 * we do not clear RETRANS, believing
			 * that retransmission is still in flight.
			 */
			if (sacked & TCPCB_LOST) {
				sacked &= ~(TCPCB_LOST|TCPCB_SACKED_RETRANS);
				tp->lost_out -= pcount;
				tp->retrans_out -= pcount;
			}
		} else {
			if (!(sacked & TCPCB_RETRANS)) { // 接收到对其SACK确认
				/* New sack for not retransmitted frame,
				 * which was in hole. It is reordering.
				 */
				// 其序号小于已经存在的最高SACK确认序号，表明发生了乱序，因为其本应当已经被SACK确认
				if (before(start_seq,
					   tcp_highest_sack_seq(tp)) &&
				    before(start_seq, state->reord))
				    // 更新乱序源头reord
					state->reord = start_seq;

				if (!after(end_seq, tp->high_seq))
					state->flag |= FLAG_ORIG_SACK_ACKED;
				if (state->first_sackt == 0)
					state->first_sackt = xmit_time;
				state->last_sackt = xmit_time;
			}

			if (sacked & TCPCB_LOST) {
				sacked &= ~TCPCB_LOST;
				tp->lost_out -= pcount;
			}
		}

		sacked |= TCPCB_SACKED_ACKED;
		state->flag |= FLAG_DATA_SACKED;
		tp->sacked_out += pcount;
		tp->delivered += pcount;  /* Out-of-order packets delivered */

		/* Lost marker hint past SACKed? Tweak RFC3517 cnt */
		if (tp->lost_skb_hint &&
		    before(start_seq, TCP_SKB_CB(tp->lost_skb_hint)->seq))
			tp->lost_cnt_hint += pcount;
	}

	/* D-SACK. We can detect redundant retransmission in S|R and plain R
	 * frames and clear it. undo_retrans is decreased above, L|R frames
	 * are accounted above as well.
	 */
	if (dup_sack && (sacked & TCPCB_SACKED_RETRANS)) {
		sacked &= ~TCPCB_SACKED_RETRANS;
		tp->retrans_out -= pcount;
	}

	return sacked;
}

/* Shift newly-SACKed bytes from this skb to the immediately previous
 * already-SACKed sk_buff. Mark the newly-SACKed bytes as such.
 */
static bool tcp_shifted_skb(struct sock *sk, struct sk_buff *prev,
			    struct sk_buff *skb,
			    struct tcp_sacktag_state *state,
			    unsigned int pcount, int shifted, int mss,
			    bool dup_sack)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 start_seq = TCP_SKB_CB(skb)->seq;	/* start of newly-SACKed */
	u32 end_seq = start_seq + shifted;	/* end of newly-SACKed */

	BUG_ON(!pcount);

	/* Adjust counters and hints for the newly sacked sequence
	 * range but discard the return value since prev is already
	 * marked. We must tag the range first because the seq
	 * advancement below implicitly advances
	 * tcp_highest_sack_seq() when skb is highest_sack.
	 */
	tcp_sacktag_one(sk, state, TCP_SKB_CB(skb)->sacked,
			start_seq, end_seq, dup_sack, pcount,
			tcp_skb_timestamp_us(skb));
	tcp_rate_skb_delivered(sk, skb, state->rate);

	if (skb == tp->lost_skb_hint)
		tp->lost_cnt_hint += pcount;

	TCP_SKB_CB(prev)->end_seq += shifted;
	TCP_SKB_CB(skb)->seq += shifted;

	tcp_skb_pcount_add(prev, pcount);
	WARN_ON_ONCE(tcp_skb_pcount(skb) < pcount);
	tcp_skb_pcount_add(skb, -pcount);

	/* When we're adding to gso_segs == 1, gso_size will be zero,
	 * in theory this shouldn't be necessary but as long as DSACK
	 * code can come after this skb later on it's better to keep
	 * setting gso_size to something.
	 */
	if (!TCP_SKB_CB(prev)->tcp_gso_size)
		TCP_SKB_CB(prev)->tcp_gso_size = mss;

	/* CHECKME: To clear or not to clear? Mimics normal skb currently */
	if (tcp_skb_pcount(skb) <= 1)
		TCP_SKB_CB(skb)->tcp_gso_size = 0;

	/* Difference in this won't matter, both ACKed by the same cumul. ACK */
	TCP_SKB_CB(prev)->sacked |= (TCP_SKB_CB(skb)->sacked & TCPCB_EVER_RETRANS);

	if (skb->len > 0) {
		BUG_ON(!tcp_skb_pcount(skb));
		NET_INC_STATS(sock_net(sk), LINUX_MIB_SACKSHIFTED);
		return false;
	}

	/* Whole SKB was eaten :-) */

	if (skb == tp->retransmit_skb_hint)
		tp->retransmit_skb_hint = prev;
	if (skb == tp->lost_skb_hint) {
		tp->lost_skb_hint = prev;
		tp->lost_cnt_hint -= tcp_skb_pcount(prev);
	}

	TCP_SKB_CB(prev)->tcp_flags |= TCP_SKB_CB(skb)->tcp_flags;
	TCP_SKB_CB(prev)->eor = TCP_SKB_CB(skb)->eor;
	if (TCP_SKB_CB(skb)->tcp_flags & TCPHDR_FIN)
		TCP_SKB_CB(prev)->end_seq++;

	if (skb == tcp_highest_sack(sk))
		tcp_advance_highest_sack(sk, skb);

	tcp_skb_collapse_tstamp(prev, skb);
	if (unlikely(TCP_SKB_CB(prev)->tx.delivered_mstamp))
		TCP_SKB_CB(prev)->tx.delivered_mstamp = 0;

	tcp_rtx_queue_unlink_and_free(skb, sk);

	NET_INC_STATS(sock_net(sk), LINUX_MIB_SACKMERGED);

	return true;
}

/* I wish gso_size would have a bit more sane initialization than
 * something-or-zero which complicates things
 */
static int tcp_skb_seglen(const struct sk_buff *skb)
{
	return tcp_skb_pcount(skb) == 1 ? skb->len : tcp_skb_mss(skb);
}

/* Shifting pages past head area doesn't work */
static int skb_can_shift(const struct sk_buff *skb)
{
	return !skb_headlen(skb) && skb_is_nonlinear(skb);
}

int tcp_skb_shift(struct sk_buff *to, struct sk_buff *from,
		  int pcount, int shiftlen)
{
	/* TCP min gso_size is 8 bytes (TCP_MIN_GSO_SIZE)
	 * Since TCP_SKB_CB(skb)->tcp_gso_segs is 16 bits, we need
	 * to make sure not storing more than 65535 * 8 bytes per skb,
	 * even if current MSS is bigger.
	 */
	if (unlikely(to->len + shiftlen >= 65535 * TCP_MIN_GSO_SIZE))
		return 0;
	if (unlikely(tcp_skb_pcount(to) + pcount > 65535))
		return 0;
	return skb_shift(to, from, shiftlen);
}

/* Try collapsing SACK blocks spanning across multiple skbs to a single
 * skb.
 */
static struct sk_buff *tcp_shift_skb_data(struct sock *sk, struct sk_buff *skb,
					  struct tcp_sacktag_state *state,
					  u32 start_seq, u32 end_seq,
					  bool dup_sack)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *prev;
	int mss;
	int pcount = 0;
	int len;
	int in_sack;

	/* Normally R but no L won't result in plain S */
	if (!dup_sack &&
	    (TCP_SKB_CB(skb)->sacked & (TCPCB_LOST|TCPCB_SACKED_RETRANS)) == TCPCB_SACKED_RETRANS)
		goto fallback;
	if (!skb_can_shift(skb))
		goto fallback;
	/* This frame is about to be dropped (was ACKed). */
	if (!after(TCP_SKB_CB(skb)->end_seq, tp->snd_una))
		goto fallback;

	/* Can only happen with delayed DSACK + discard craziness */
	prev = skb_rb_prev(skb);
	if (!prev)
		goto fallback;

	if ((TCP_SKB_CB(prev)->sacked & TCPCB_TAGBITS) != TCPCB_SACKED_ACKED)
		goto fallback;

	if (!tcp_skb_can_collapse(prev, skb))
		goto fallback;

	in_sack = !after(start_seq, TCP_SKB_CB(skb)->seq) &&
		  !before(end_seq, TCP_SKB_CB(skb)->end_seq);

	if (in_sack) {
		len = skb->len;
		pcount = tcp_skb_pcount(skb);
		mss = tcp_skb_seglen(skb);

		/* TODO: Fix DSACKs to not fragment already SACKed and we can
		 * drop this restriction as unnecessary
		 */
		if (mss != tcp_skb_seglen(prev))
			goto fallback;
	} else {
		if (!after(TCP_SKB_CB(skb)->end_seq, start_seq))
			goto noop;
		/* CHECKME: This is non-MSS split case only?, this will
		 * cause skipped skbs due to advancing loop btw, original
		 * has that feature too
		 */
		if (tcp_skb_pcount(skb) <= 1)
			goto noop;

		in_sack = !after(start_seq, TCP_SKB_CB(skb)->seq);
		if (!in_sack) {
			/* TODO: head merge to next could be attempted here
			 * if (!after(TCP_SKB_CB(skb)->end_seq, end_seq)),
			 * though it might not be worth of the additional hassle
			 *
			 * ...we can probably just fallback to what was done
			 * previously. We could try merging non-SACKed ones
			 * as well but it probably isn't going to buy off
			 * because later SACKs might again split them, and
			 * it would make skb timestamp tracking considerably
			 * harder problem.
			 */
			goto fallback;
		}

		len = end_seq - TCP_SKB_CB(skb)->seq;
		BUG_ON(len < 0);
		BUG_ON(len > skb->len);

		/* MSS boundaries should be honoured or else pcount will
		 * severely break even though it makes things bit trickier.
		 * Optimize common case to avoid most of the divides
		 */
		mss = tcp_skb_mss(skb);

		/* TODO: Fix DSACKs to not fragment already SACKed and we can
		 * drop this restriction as unnecessary
		 */
		if (mss != tcp_skb_seglen(prev))
			goto fallback;

		if (len == mss) {
			pcount = 1;
		} else if (len < mss) {
			goto noop;
		} else {
			pcount = len / mss;
			len = pcount * mss;
		}
	}

	/* tcp_sacktag_one() won't SACK-tag ranges below snd_una */
	if (!after(TCP_SKB_CB(skb)->seq + len, tp->snd_una))
		goto fallback;

	if (!tcp_skb_shift(prev, skb, pcount, len))
		goto fallback;
	if (!tcp_shifted_skb(sk, prev, skb, state, pcount, len, mss, dup_sack))
		goto out;

	/* Hole filled allows collapsing with the next as well, this is very
	 * useful when hole on every nth skb pattern happens
	 */
	skb = skb_rb_next(prev);
	if (!skb)
		goto out;

	if (!skb_can_shift(skb) ||
	    ((TCP_SKB_CB(skb)->sacked & TCPCB_TAGBITS) != TCPCB_SACKED_ACKED) ||
	    (mss != tcp_skb_seglen(skb)))
		goto out;

	len = skb->len;
	pcount = tcp_skb_pcount(skb);
	if (tcp_skb_shift(prev, skb, pcount, len))
		tcp_shifted_skb(sk, prev, skb, state, pcount,
				len, mss, 0);

out:
	return prev;

noop:
	return skb;

fallback:
	NET_INC_STATS(sock_net(sk), LINUX_MIB_SACKSHIFTFALLBACK);
	return NULL;
}

static struct sk_buff *tcp_sacktag_walk(struct sk_buff *skb, struct sock *sk,
					struct tcp_sack_block *next_dup,
					struct tcp_sacktag_state *state,
					u32 start_seq, u32 end_seq,
					bool dup_sack_in)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *tmp;

	skb_rbtree_walk_from(skb) {
		int in_sack = 0;
		bool dup_sack = dup_sack_in;

		/* queue is in-order => we can short-circuit the walk early */
		if (!before(TCP_SKB_CB(skb)->seq, end_seq))
			break;

		if (next_dup  &&
		    before(TCP_SKB_CB(skb)->seq, next_dup->end_seq)) {
			in_sack = tcp_match_skb_to_sack(sk, skb,
							next_dup->start_seq,
							next_dup->end_seq);
			if (in_sack > 0)
				dup_sack = true;
		}

		/* skb reference here is a bit tricky to get right, since
		 * shifting can eat and free both this skb and the next,
		 * so not even _safe variant of the loop is enough.
		 */
		if (in_sack <= 0) {
			tmp = tcp_shift_skb_data(sk, skb, state,
						 start_seq, end_seq, dup_sack);
			if (tmp) {
				if (tmp != skb) {
					skb = tmp;
					continue;
				}

				in_sack = 0;
			} else {
				in_sack = tcp_match_skb_to_sack(sk, skb,
								start_seq,
								end_seq);
			}
		}

		if (unlikely(in_sack < 0))
			break;

		if (in_sack) {
			TCP_SKB_CB(skb)->sacked =
				tcp_sacktag_one(sk,
						state,
						TCP_SKB_CB(skb)->sacked,
						TCP_SKB_CB(skb)->seq,
						TCP_SKB_CB(skb)->end_seq,
						dup_sack,
						tcp_skb_pcount(skb),
						tcp_skb_timestamp_us(skb));
			tcp_rate_skb_delivered(sk, skb, state->rate);
			if (TCP_SKB_CB(skb)->sacked & TCPCB_SACKED_ACKED)
				list_del_init(&skb->tcp_tsorted_anchor);

			if (!before(TCP_SKB_CB(skb)->seq,
				    tcp_highest_sack_seq(tp)))
				tcp_advance_highest_sack(sk, skb);
		}
	}
	return skb;
}

static struct sk_buff *tcp_sacktag_bsearch(struct sock *sk, u32 seq)
{
	struct rb_node *parent, **p = &sk->tcp_rtx_queue.rb_node;
	struct sk_buff *skb;

	while (*p) {
		parent = *p;
		skb = rb_to_skb(parent);
		if (before(seq, TCP_SKB_CB(skb)->seq)) {
			p = &parent->rb_left;
			continue;
		}
		if (!before(seq, TCP_SKB_CB(skb)->end_seq)) {
			p = &parent->rb_right;
			continue;
		}
		return skb;
	}
	return NULL;
}

static struct sk_buff *tcp_sacktag_skip(struct sk_buff *skb, struct sock *sk,
					u32 skip_to_seq)
{
	if (skb && after(TCP_SKB_CB(skb)->seq, skip_to_seq))
		return skb;

	return tcp_sacktag_bsearch(sk, skip_to_seq);
}

static struct sk_buff *tcp_maybe_skipping_dsack(struct sk_buff *skb,
						struct sock *sk,
						struct tcp_sack_block *next_dup,
						struct tcp_sacktag_state *state,
						u32 skip_to_seq)
{
	if (!next_dup)
		return skb;

	if (before(next_dup->start_seq, skip_to_seq)) {
		skb = tcp_sacktag_skip(skb, sk, next_dup->start_seq);
		skb = tcp_sacktag_walk(skb, sk, NULL, state,
				       next_dup->start_seq, next_dup->end_seq,
				       1);
	}

	return skb;
}

static int tcp_sack_cache_ok(const struct tcp_sock *tp, const struct tcp_sack_block *cache)
{
	return cache < tp->recv_sack_cache + ARRAY_SIZE(tp->recv_sack_cache);
}

static int
tcp_sacktag_write_queue(struct sock *sk, const struct sk_buff *ack_skb,
			u32 prior_snd_una, struct tcp_sacktag_state *state)
{
	struct tcp_sock *tp = tcp_sk(sk);
	const unsigned char *ptr = (skb_transport_header(ack_skb) +
				    TCP_SKB_CB(ack_skb)->sacked);
	struct tcp_sack_block_wire *sp_wire = (struct tcp_sack_block_wire *)(ptr+2);
	struct tcp_sack_block sp[TCP_NUM_SACKS];
	struct tcp_sack_block *cache;
	struct sk_buff *skb;
	int num_sacks = min(TCP_NUM_SACKS, (ptr[1] - TCPOLEN_SACK_BASE) >> 3);
	int used_sacks;
	bool found_dup_sack = false;
	int i, j;
	int first_sack_index;

	state->flag = 0;
	state->reord = tp->snd_nxt;

	if (!tp->sacked_out)
		tcp_highest_sack_reset(sk);

	found_dup_sack = tcp_check_dsack(sk, ack_skb, sp_wire,
					 num_sacks, prior_snd_una);
	if (found_dup_sack) {
		state->flag |= FLAG_DSACKING_ACK;
		tp->delivered++; /* A spurious retransmission is delivered */
	}

	/* Eliminate too old ACKs, but take into
	 * account more or less fresh ones, they can
	 * contain valid SACK info.
	 */
	if (before(TCP_SKB_CB(ack_skb)->ack_seq, prior_snd_una - tp->max_window))
		return 0;

	if (!tp->packets_out)
		goto out;

	used_sacks = 0;
	first_sack_index = 0;
	for (i = 0; i < num_sacks; i++) {
		bool dup_sack = !i && found_dup_sack;

		sp[used_sacks].start_seq = get_unaligned_be32(&sp_wire[i].start_seq);
		sp[used_sacks].end_seq = get_unaligned_be32(&sp_wire[i].end_seq);

		if (!tcp_is_sackblock_valid(tp, dup_sack,
					    sp[used_sacks].start_seq,
					    sp[used_sacks].end_seq)) {
			int mib_idx;

			if (dup_sack) {
				if (!tp->undo_marker)
					mib_idx = LINUX_MIB_TCPDSACKIGNOREDNOUNDO;
				else
					mib_idx = LINUX_MIB_TCPDSACKIGNOREDOLD;
			} else {
				/* Don't count olds caused by ACK reordering */
				if ((TCP_SKB_CB(ack_skb)->ack_seq != tp->snd_una) &&
				    !after(sp[used_sacks].end_seq, tp->snd_una))
					continue;
				mib_idx = LINUX_MIB_TCPSACKDISCARD;
			}

			NET_INC_STATS(sock_net(sk), mib_idx);
			if (i == 0)
				first_sack_index = -1;
			continue;
		}

		/* Ignore very old stuff early */
		if (!after(sp[used_sacks].end_seq, prior_snd_una)) {
			if (i == 0)
				first_sack_index = -1;
			continue;
		}

		used_sacks++;
	}

	/* order SACK blocks to allow in order walk of the retrans queue */
	for (i = used_sacks - 1; i > 0; i--) {
		for (j = 0; j < i; j++) {
			if (after(sp[j].start_seq, sp[j + 1].start_seq)) {
				swap(sp[j], sp[j + 1]);

				/* Track where the first SACK block goes to */
				if (j == first_sack_index)
					first_sack_index = j + 1;
			}
		}
	}

	state->mss_now = tcp_current_mss(sk);
	skb = NULL;
	i = 0;

	if (!tp->sacked_out) {
		/* It's already past, so skip checking against it */
		cache = tp->recv_sack_cache + ARRAY_SIZE(tp->recv_sack_cache);
	} else {
		cache = tp->recv_sack_cache;
		/* Skip empty blocks in at head of the cache */
		while (tcp_sack_cache_ok(tp, cache) && !cache->start_seq &&
		       !cache->end_seq)
			cache++;
	}

	while (i < used_sacks) {
		u32 start_seq = sp[i].start_seq;
		u32 end_seq = sp[i].end_seq;
		bool dup_sack = (found_dup_sack && (i == first_sack_index));
		struct tcp_sack_block *next_dup = NULL;

		if (found_dup_sack && ((i + 1) == first_sack_index))
			next_dup = &sp[i + 1];

		/* Skip too early cached blocks */
		while (tcp_sack_cache_ok(tp, cache) &&
		       !before(start_seq, cache->end_seq))
			cache++;

		/* Can skip some work by looking recv_sack_cache? */
		if (tcp_sack_cache_ok(tp, cache) && !dup_sack &&
		    after(end_seq, cache->start_seq)) {

			/* Head todo? */
			if (before(start_seq, cache->start_seq)) {
				skb = tcp_sacktag_skip(skb, sk, start_seq);
				skb = tcp_sacktag_walk(skb, sk, next_dup,
						       state,
						       start_seq,
						       cache->start_seq,
						       dup_sack);
			}

			/* Rest of the block already fully processed? */
			if (!after(end_seq, cache->end_seq))
				goto advance_sp;

			skb = tcp_maybe_skipping_dsack(skb, sk, next_dup,
						       state,
						       cache->end_seq);

			/* ...tail remains todo... */
			if (tcp_highest_sack_seq(tp) == cache->end_seq) {
				/* ...but better entrypoint exists! */
				skb = tcp_highest_sack(sk);
				if (!skb)
					break;
				cache++;
				goto walk;
			}

			skb = tcp_sacktag_skip(skb, sk, cache->end_seq);
			/* Check overlap against next cached too (past this one already) */
			cache++;
			continue;
		}

		if (!before(start_seq, tcp_highest_sack_seq(tp))) {
			skb = tcp_highest_sack(sk);
			if (!skb)
				break;
		}
		skb = tcp_sacktag_skip(skb, sk, start_seq);

walk:
		skb = tcp_sacktag_walk(skb, sk, next_dup, state,
				       start_seq, end_seq, dup_sack);

advance_sp:
		i++;
	}

	/* Clear the head of the cache sack blocks so we can skip it next time */
	for (i = 0; i < ARRAY_SIZE(tp->recv_sack_cache) - used_sacks; i++) {
		tp->recv_sack_cache[i].start_seq = 0;
		tp->recv_sack_cache[i].end_seq = 0;
	}
	for (j = 0; j < used_sacks; j++)
		tp->recv_sack_cache[i++] = sp[j];

	if (inet_csk(sk)->icsk_ca_state != TCP_CA_Loss || tp->undo_marker)
	    // 当前的拥塞状态等于TCP_CA_Loss，并且没有处在可撤销阶段，不必更新乱序级别。否则，进行更新。
	    // 初始情况下reord的值设置为SND.NXT的值，即发送报文的最大序号，这里首先假设不会发生乱序的情况
		tcp_check_sack_reordering(sk, state->reord, 0);

	tcp_verify_left_out(tp);
out:

#if FASTRETRANS_DEBUG > 0
	WARN_ON((int)tp->sacked_out < 0);
	WARN_ON((int)tp->lost_out < 0);
	WARN_ON((int)tp->retrans_out < 0);
	WARN_ON((int)tcp_packets_in_flight(tp) < 0);
#endif
	return state->flag;
}

/* Limits sacked_out so that sum with lost_out isn't ever larger than
 * packets_out. Returns false if sacked_out adjustement wasn't necessary.
 */
static bool tcp_limit_reno_sacked(struct tcp_sock *tp)
{
	u32 holes;

	holes = max(tp->lost_out, 1U);
	holes = min(holes, tp->packets_out);

	if ((tp->sacked_out + holes) > tp->packets_out) {
		tp->sacked_out = tp->packets_out - holes;
		return true;
	}
	return false;
}

/* If we receive more dupacks than we expected counting segments
 * in assumption of absent reordering, interpret this as reordering.
 * The only another reason could be bug in receiver TCP.
 */
static void tcp_check_reno_reordering(struct sock *sk, const int addend)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (!tcp_limit_reno_sacked(tp))
		return;

	tp->reordering = min_t(u32, tp->packets_out + addend,
			       sock_net(sk)->ipv4.sysctl_tcp_max_reordering);
	tp->reord_seen++;
	NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPRENOREORDER);
}

/* Emulate SACKs for SACKless connection: account for a new dupack. */

static void tcp_add_reno_sack(struct sock *sk, int num_dupack)
{
	if (num_dupack) {
		struct tcp_sock *tp = tcp_sk(sk);
		u32 prior_sacked = tp->sacked_out;
		s32 delivered;

		tp->sacked_out += num_dupack;
		tcp_check_reno_reordering(sk, 0);
		delivered = tp->sacked_out - prior_sacked;
		if (delivered > 0)
			tp->delivered += delivered;
		tcp_verify_left_out(tp);
	}
}

/* Account for ACK, ACKing some data in Reno Recovery phase. */

static void tcp_remove_reno_sacks(struct sock *sk, int acked)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (acked > 0) {
		/* One ACK acked hole. The rest eat duplicate ACKs. */
		tp->delivered += max_t(int, acked - tp->sacked_out, 1);
		if (acked - 1 >= tp->sacked_out)
			tp->sacked_out = 0;
		else
			tp->sacked_out -= acked - 1;
	}
	tcp_check_reno_reordering(sk, acked);
	tcp_verify_left_out(tp);
}

static inline void tcp_reset_reno_sack(struct tcp_sock *tp)
{
	tp->sacked_out = 0;
}

void tcp_clear_retrans(struct tcp_sock *tp)
{
	tp->retrans_out = 0;
	tp->lost_out = 0;
	tp->undo_marker = 0;
	tp->undo_retrans = -1;
	tp->sacked_out = 0;
}

static inline void tcp_init_undo(struct tcp_sock *tp)
{
	tp->undo_marker = tp->snd_una;
	/* Retransmission still in flight may cause DSACKs later. */
	tp->undo_retrans = tp->retrans_out ? : -1;
}

static bool tcp_is_rack(const struct sock *sk)
{
	return sock_net(sk)->ipv4.sysctl_tcp_recovery & TCP_RACK_LOSS_DETECTION;
}

/* If we detect SACK reneging, forget all SACK information
 * and reset tags completely, otherwise preserve SACKs. If receiver
 * dropped its ofo queue, we will know this due to reneging detection.
 */
/*
 * 如果SACK确认了重传队列首部的报文（本该由ACK.SEQ确认），表明对端丢弃了其OFO队列
 * 如果队列的首个报文skb被SACK确认过，即sacked具有标记TCPCB_SACKED_ACKED，表明接收端发生了SACKRENEGING，
 * 清空了乱序队列。
 * 这里需要清除接收到的SACK信息。
 */
static void tcp_timeout_mark_lost(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *skb, *head;
	bool is_reneg;			/* is receiver reneging on SACKs? */

	head = tcp_rtx_queue_head(sk);
	// 队列的首个报文skb被SACK确认过，即sacked具有标记TCPCB_SACKED_ACKED，表明接收端发生了SACKRENEGING
	is_reneg = head && (TCP_SKB_CB(head)->sacked & TCPCB_SACKED_ACKED);
	if (is_reneg) {
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPSACKRENEGING);
		tp->sacked_out = 0;
		/* Mark SACK reneging until we recover from this loss event. */
		tp->is_sack_reneg = 1;
	} else if (tcp_is_reno(tp)) {
		tcp_reset_reno_sack(tp);
	}

	/*
	 * 遍历套接口重传队列，
	 * 如果依据RACK算法，报文并没有超时，不标记，
	 * 否则，调用函数tcp_mark_skb_lost对重传队列中的报文进行丢失标记。
	 */
	skb = head;
	skb_rbtree_walk_from(skb) {
		if (is_reneg) // 发生了reneging，清除TCPCB_SACKED_ACKED标记
			TCP_SKB_CB(skb)->sacked &= ~TCPCB_SACKED_ACKED;
		else if (tcp_is_rack(sk) && skb != head &&
			 tcp_rack_skb_timeout(tp, skb, 0) > 0)
			continue; /* Don't mark recently sent ones lost yet */
		tcp_mark_skb_lost(sk, skb);
	}
	tcp_verify_left_out(tp);
	tcp_clear_all_retrans_hints(tp);/* 虽然在tcp_verify_retransmit_hint函数中设置了retransmit_skb_hint指针，
	 * 但是，这里又做了清除此指针的操作。 */
}

/* Enter Loss state. */
/* Enter Loss state. If we detect SACK reneging, forget all SACK information
 * and reset tags completely, otherwise preserve SACKs. If receiver
 * dropped its ofo queue, we will know this due to reneging detection.
 有关slow start以及Congestion avoidance算法描述可以看rfc2001:
http://www.faqs.org/rfcs/rfc2001.html
 CWND - Sender side limit
 RWND - Receiver side limit
 Slow start threshold ( SSTHRESH ) - Used to determine whether slow start is used or congestion avoidance
 When starting, probe slowly - IW <= 2 * SMSS
 Initial size of SSTHRESH can be arbitrarily high, as high as the RWND
 Use slow start when SSTHRESH > CWND. Else, use Congestion avoidance
 Slow start - CWND is increased by an amount less than or equal to the SMSS for every ACK
 Congestion avoidance - CWND += SMSS*SMSS/CWND
 When loss is detected - SSTHRESH = max( FlightSize/2, 2*SMSS )

 在传输过程中，client 和 server 协商接收窗口 rwnd，再结合拥塞控制窗口 cwnd 计算滑动窗口 swnd。
 在 Linux 内核实现中，滑动窗口 cwnd 是以包pkt mss为单位，所以在计算 swnd 时需要乘上 mss（最大分段大小）
 swnd = min(rwnd, cwnd * mss)
 */
// 进入Loss状态 这个函数主要用来标记丢失的段(也就是没有acked的段),然后通过执行slow start来降低传输速率.
void tcp_enter_loss(struct sock *sk)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	struct net *net = sock_net(sk);
	bool new_recovery = icsk->icsk_ca_state < TCP_CA_Recovery;

	tcp_timeout_mark_lost(sk);

	/* Reduce ssthresh if it has not yet been made inside this window. */
    /* 1 拥塞控制状态小于TCP_CA_Disorder，即还未进入恢复或者丢失拥塞状态
     * 2 high_seq(拥塞开始时的下一个将要发送的序列号)不在SND.UNA(发送未确认的序列号)之后，即当前没有未完成的拥塞处理
     * 3 状态为TCP_CA_Loss，并且还未重新传输过。
     * 如果有一个满足说明有数据丢失,因此降低threshold。
     */
	if (icsk->icsk_ca_state <= TCP_CA_Disorder ||
	    !after(tp->high_seq, tp->snd_una) ||
	    (icsk->icsk_ca_state == TCP_CA_Loss && !icsk->icsk_retransmits)) {
        /* 保留当前阈值，以便在拥塞窗口调整撤销时使用 */
		tp->prior_ssthresh = tcp_current_ssthresh(sk);
		tp->prior_cwnd = tp->snd_cwnd;
        /* 减小慢启动阈值*/
		tp->snd_ssthresh = icsk->icsk_ca_ops->ssthresh(sk);
        /* 通知CA_EVENT_LOSS事件给具体的拥塞控制算法 */
		tcp_ca_event(sk, CA_EVENT_LOSS);
		tcp_init_undo(tp); // 初始化拥塞撤销操作,以便FRTO或者Eifel算法检测到为不必要的超时（RTO值过小）后，恢复之前的拥塞状态
	}
	tp->snd_cwnd	   = tcp_packets_in_flight(tp) + 1; /* 调整拥塞窗口 */
	tp->snd_cwnd_cnt   = 0;                             // 上次调整拥塞窗口后 到目前位置接收到的总ack段数
	tp->snd_cwnd_stamp = tcp_jiffies32;                 // 设置时间

	/* Timeout in disordered state after receiving substantial DUPACKs
	 * suggests that the degree of reordering is over-estimated.
	 */
	if (icsk->icsk_ca_state <= TCP_CA_Disorder &&
	    tp->sacked_out >= net->ipv4.sysctl_tcp_reordering)
		tp->reordering = min_t(unsigned int, tp->reordering,
				       net->ipv4.sysctl_tcp_reordering);
	tcp_set_ca_state(sk, TCP_CA_Loss);
	tp->high_seq = tp->snd_nxt; // 以示RTO超时恢复正在进行。
	tcp_ecn_queue_cwr(tp); /* 表示发送发进入拥塞状态 */

	/* F-RTO RFC5682 sec 3.1 step 1: retransmit SND.UNA if no previous
	 * loss recovery is underway except recurring timeout(s) on
	 * the same SND.UNA (sec 3.2). Disable F-RTO on path MTU probing
	 */
    // 如果已经在loss/recovery状态或者网络上有重传包，则收到重传包的ack会导致frto误判，认为超时是spurious
	tp->frto = net->ipv4.sysctl_tcp_frto &&
		   (new_recovery || icsk->icsk_retransmits) && // rto超时前不在recovery状态，或者重传过
		   !inet_csk(sk)->icsk_mtup.probe_size;        // 没有在mtu探测
}

/* If ACK arrived pointing to a remembered SACK, it means that our
 * remembered SACKs do not reflect real state of receiver i.e.
 * receiver _host_ is heavily congested (or buggy).
 *
 * To avoid big spurious retransmission bursts due to transient SACK
 * scoreboard oddities that look like reneging, we give the receiver a
 * little time (max(RTT/2, 10ms)) to send us some more ACKs that will
 * restore sanity to the SACK scoreboard. If the apparent reneging
 * persists until this RTO then we'll clear the SACK scoreboard.
 */
/*
 * 如果接收到的确认 ACK 指向之前记录的 SACK，这说明之前记录的 SACK 并没有反映接收方的真实状态。
 * 接收路径上很有可能已经有拥塞发生或者接收主机正在经历严重的拥塞甚至处理出现了 BUG，
 * 因为按照正常的逻辑流程，接收的 ACK 不应该指向已记录的 SACK，而应该指向 SACK 后面未接收的地方。
 * 通常情况下，此时接收方已经删除了保存到失序队列中的段。
 * 为了避免短暂奇怪的看起来像是违约的 SACK 导致更大量的重传，我们给接收者一些时间,
 * 即 max(RTT/2; 10ms) 以便于让他可以给我们更多的 ACK，从而可以使得SACK 的记分板变得正常一点。
 * 如果这个表面上的违约一直持续到重传时间结束，我们就把 SACK 的记分板清除掉.
 * Reneging 的意思就是违约，接收方有权把已经报给发送端 SACK 里的数据给丢了。
 * 当然，我们肯定是不鼓励这样做的，因为这个事会把问题复杂化。
 * 但是，接收方可能会由于一些极端情况这么做，比如要把内存给别的更重要的东西。
 * 所以，发送方也不能完全依赖 SACK，主要还是要依赖 ACK，并维护 Time-Out。
 * 如果后续的 ACK 没有增长，那么还是要把 SACK 的东西重传，另外，接收端这边永远不能把 SACK 的包标记为 Ack。　　
 * 注意：SACK 会消费发送方的资源，试想，如果一个攻击者给数据发送方发一堆 SACK 的选项，
 * 这会导致发送方开始要重传甚至遍历已经发出的数据，这会消耗很多发送端的资源
 */
static bool tcp_check_sack_reneging(struct sock *sk, int flag)
{
	if (flag & FLAG_SACK_RENEGING) { // 接收方发生了sack reneging
		struct tcp_sock *tp = tcp_sk(sk);
        // 为了避免不必要的重传，我们等待一段很短的时间，
        // 等待接收端发送更多的ACK报文，期待后续ACK确认SACK中序号。
        // 定时器时长为RTT的一半，但是不超过10ms。
        // 注意套接口中变量srtt_us中保存的为RTT的8倍值。
		unsigned long delay = max(usecs_to_jiffies(tp->srtt_us >> 4),
					  msecs_to_jiffies(10)); // 计算超时重传时间
        // 更新超时重传定时器
		inet_csk_reset_xmit_timer(sk, ICSK_TIME_RETRANS,
					  delay, TCP_RTO_MAX);
		return true;
	}
	return false;
}

/* Heurestics to calculate number of duplicate ACKs. There's no dupACKs
 * counter when SACK is enabled (without SACK, sacked_out is used for
 * that purpose).
 *
 * With reordering, holes may still be in flight, so RFC3517 recovery
 * uses pure sacked_out (total number of SACKed segments) even though
 * it violates the RFC that uses duplicate ACKs, often these are equal
 * but when e.g. out-of-window ACKs or packet duplication occurs,
 * they differ. Since neither occurs due to loss, TCP should really
 * ignore them.
 */
static inline int tcp_dupack_heuristics(const struct tcp_sock *tp)
{
	return tp->sacked_out + 1;
}

/* Linux NewReno/SACK/ECN state machine.
 * --------------------------------------
 *
 * "Open"	Normal state, no dubious events, fast path.
 * "Disorder"   In all the respects it is "Open",
 *		but requires a bit more attention. It is entered when
 *		we see some SACKs or dupacks. It is split of "Open"
 *		mainly to move some processing from fast path to slow one.
 * "CWR"	CWND was reduced due to some Congestion Notification event.
 *		It can be ECN, ICMP source quench, local device congestion.
 * "Recovery"	CWND was reduced, we are fast-retransmitting.
 * "Loss"	CWND was reduced due to RTO timeout or SACK reneging.
 *
 * tcp_fastretrans_alert() is entered:
 * - each incoming ACK, if state is not "Open"
 * - when arrived ACK is unusual, namely:
 *	* SACK
 *	* Duplicate ACK.
 *	* ECN ECE.
 *
 * Counting packets in flight is pretty simple.
 *
 *	in_flight = packets_out - left_out + retrans_out
 *
 *	packets_out is SND.NXT-SND.UNA counted in packets.
 *
 *	retrans_out is number of retransmitted segments.
 *
 *	left_out is number of segments left network, but not ACKed yet.
 *
 *		left_out = sacked_out + lost_out
 *
 *     sacked_out: Packets, which arrived to receiver out of order
 *		   and hence not ACKed. With SACKs this number is simply
 *		   amount of SACKed data. Even without SACKs
 *		   it is easy to give pretty reliable estimate of this number,
 *		   counting duplicate ACKs.
 *
 *       lost_out: Packets lost by network. TCP has no explicit
 *		   "loss notification" feedback from network (for now).
 *		   It means that this number can be only _guessed_.
 *		   Actually, it is the heuristics to predict lossage that
 *		   distinguishes different algorithms.
 *
 *	F.e. after RTO, when all the queue is considered as lost,
 *	lost_out = packets_out and in_flight = retrans_out.
 *
 *		Essentially, we have now a few algorithms detecting
 *		lost packets.
 *
 *		If the receiver supports SACK:
 *
 *		RFC6675/3517: It is the conventional algorithm. A packet is
 *		considered lost if the number of higher sequence packets
 *		SACKed is greater than or equal the DUPACK thoreshold
 *		(reordering). This is implemented in tcp_mark_head_lost and
 *		tcp_update_scoreboard.
 *
 *		RACK (draft-ietf-tcpm-rack-01): it is a newer algorithm
 *		(2017-) that checks timing instead of counting DUPACKs.
 *		Essentially a packet is considered lost if it's not S/ACKed
 *		after RTT + reordering_window, where both metrics are
 *		dynamically measured and adjusted. This is implemented in
 *		tcp_rack_mark_lost.
 *
 *		If the receiver does not support SACK:
 *
 *		NewReno (RFC6582): in Recovery we assume that one segment
 *		is lost (classic Reno). While we are in Recovery and
 *		a partial ACK arrives, we assume that one more packet
 *		is lost (NewReno). This heuristics are the same in NewReno
 *		and SACK.
 *
 * Really tricky (and requiring careful tuning) part of algorithm
 * is hidden in functions tcp_time_to_recover() and tcp_xmit_retransmit_queue().
 * The first determines the moment _when_ we should reduce CWND and,
 * hence, slow down forward transmission. In fact, it determines the moment
 * when we decide that hole is caused by loss, rather than by a reorder.
 *
 * tcp_xmit_retransmit_queue() decides, _what_ we should retransmit to fill
 * holes, caused by lost packets.
 *
 * And the most logically complicated part of algorithm is undo
 * heuristics. We detect false retransmits due to both too early
 * fast retransmit (reordering) and underestimated RTO, analyzing
 * timestamps and D-SACKs. When we detect that some segments were
 * retransmitted by mistake and CWND reduction was wrong, we undo
 * window reduction and abort recovery phase. This logic is hidden
 * inside several functions named tcp_try_undo_<something>.
 */

/* This function decides, when we should leave Disordered state
 * and enter Recovery phase, reducing congestion window.
 *
 * Main question: may we further continue forward transmission
 * with the same cwnd?
 */
// 丢包（lost_out），或者dupacks数量超出乱序级别，需要进入TCP_CA_Recovery状态
static bool tcp_time_to_recover(struct sock *sk, int flag)
{
	struct tcp_sock *tp = tcp_sk(sk);

	/* Trick#1: The loss is proven. */
	if (tp->lost_out)
	    // 有丢包（lost_out）
		return true;

	/* Not-A-Trick#2 : Classic rule... */
	if (!tcp_is_rack(sk) && tcp_dupack_heuristics(tp) > tp->reordering)
	    // dupacks数量超出乱序级别，需要进入TCP_CA_Recovery状态
		return true;

	return false;
}

/* Detect loss in event "A" above by marking head of queue up as lost.
 * For RFC3517 SACK, a segment is considered lost if it
 * has at least tp->reordering SACKed seqments above it; "packets" refers to
 * the maximum SACKed segments to pass before reaching this limit.
 */
static void tcp_mark_head_lost(struct sock *sk, int packets, int mark_head)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *skb;
	int cnt;
	/* Use SACK to deduce losses of new sequences sent during recovery */
	const u32 loss_high = tp->snd_nxt;

	WARN_ON(packets > tp->packets_out);
	skb = tp->lost_skb_hint;
	if (skb) {
		/* Head already handled? */
		if (mark_head && after(TCP_SKB_CB(skb)->seq, tp->snd_una))
			return;
		cnt = tp->lost_cnt_hint;
	} else {
		skb = tcp_rtx_queue_head(sk);
		cnt = 0;
	}

	skb_rbtree_walk_from(skb) {
		/* TODO: do this better */
		/* this is not the most efficient way to do this... */
		tp->lost_skb_hint = skb;
		tp->lost_cnt_hint = cnt;

		if (after(TCP_SKB_CB(skb)->end_seq, loss_high)) // 当前遍历报文的结束序号位于最高的丢包序号之后
			break;

		if (TCP_SKB_CB(skb)->sacked & TCPCB_SACKED_ACKED)
			cnt += tcp_skb_pcount(skb);

		if (cnt > packets) // 当前遍历的SACK所确认报文数量达到要求的packets值
			break;

		tcp_skb_mark_lost(tp, skb);

		if (mark_head)
			break;
	}
	tcp_verify_left_out(tp);
}

/* Account newly detected lost packet(s) */

static void tcp_update_scoreboard(struct sock *sk, int fast_rexmit)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (tcp_is_sack(tp)) {
	    // TCP套接口协商了SACK（非Reno/NewReno）
		int sacked_upto = tp->sacked_out - tp->reordering; // 丢失的报文中所包含的SACK确认报文的数量
		if (sacked_upto >= 0)
		    // SACK确认的报文数量大于乱序级别，即认为最早发送的报文已经丢失
			tcp_mark_head_lost(sk, sacked_upto, 0);
		else if (fast_rexmit)
			tcp_mark_head_lost(sk, 1, 1); // 仅将重传队列头部的首个报文标记为丢失
	}
}

static bool tcp_tsopt_ecr_before(const struct tcp_sock *tp, u32 when)
{
	return tp->rx_opt.saw_tstamp && tp->rx_opt.rcv_tsecr &&
	       before(tp->rx_opt.rcv_tsecr, when);
}

/* skb is spurious retransmitted if the returned timestamp echo
 * reply is prior to the skb transmission time
 */
static bool tcp_skb_spurious_retrans(const struct tcp_sock *tp,
				     const struct sk_buff *skb)
{
	return (TCP_SKB_CB(skb)->sacked & TCPCB_RETRANS) &&
	       tcp_tsopt_ecr_before(tp, tcp_skb_timestamp(skb));
}

/* Nothing was retransmitted or returned timestamp is less
 * than timestamp of the first retransmission.
 * 传了之后还没有接收到对方发送的确认
 * !tp->retrans_stamp 表示已经使用F-RTO进行处理。
 * tcp_tsopt_ecr_before 表示收到ACK的时间戳和重发数据包的时间戳之前
 */
static inline bool tcp_packet_delayed(const struct tcp_sock *tp)
{
	return tp->retrans_stamp &&
	       tcp_tsopt_ecr_before(tp, tp->retrans_stamp);
}

/* Undo procedures. */

/* We can clear retrans_stamp when there are no retransmissions in the
 * window. It would seem that it is trivially available for us in
 * tp->retrans_out, however, that kind of assumptions doesn't consider
 * what will happen if errors occur when sending retransmission for the
 * second time. ...It could the that such segment has only
 * TCPCB_EVER_RETRANS set at the present time. It seems that checking
 * the head skb is enough except for some reneging corner cases that
 * are not worth the effort.
 *
 * Main reason for all this complexity is the fact that connection dying
 * time now depends on the validity of the retrans_stamp, in particular,
 * that successive retransmissions of a segment must not advance
 * retrans_stamp under any conditions.
 */
static bool tcp_any_retrans_done(const struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *skb;

	if (tp->retrans_out)
		return true;

	skb = tcp_rtx_queue_head(sk);
	if (unlikely(skb && TCP_SKB_CB(skb)->sacked & TCPCB_EVER_RETRANS))
		return true;

	return false;
}

static void DBGUNDO(struct sock *sk, const char *msg)
{
#if FASTRETRANS_DEBUG > 1
	struct tcp_sock *tp = tcp_sk(sk);
	struct inet_sock *inet = inet_sk(sk);

	if (sk->sk_family == AF_INET) {
		pr_debug("Undo %s %pI4/%u c%u l%u ss%u/%u p%u\n",
			 msg,
			 &inet->inet_daddr, ntohs(inet->inet_dport),
			 tp->snd_cwnd, tcp_left_out(tp),
			 tp->snd_ssthresh, tp->prior_ssthresh,
			 tp->packets_out);
	}
#if IS_ENABLED(CONFIG_IPV6)
	else if (sk->sk_family == AF_INET6) {
		pr_debug("Undo %s %pI6/%u c%u l%u ss%u/%u p%u\n",
			 msg,
			 &sk->sk_v6_daddr, ntohs(inet->inet_dport),
			 tp->snd_cwnd, tcp_left_out(tp),
			 tp->snd_ssthresh, tp->prior_ssthresh,
			 tp->packets_out);
	}
#endif
#endif
}

// 此函数!before(tp->snd_una, tp->high_seq)条件成立的前提下，也就是 ack 的序号已经大于拥塞开始时的 high_seq
static void tcp_undo_cwnd_reduction(struct sock *sk, bool unmark_loss)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (unmark_loss) { // 是否取消lost 报文丢失 标志
		struct sk_buff *skb;

		skb_rbtree_walk(skb, &sk->tcp_rtx_queue) {
			TCP_SKB_CB(skb)->sacked &= ~TCPCB_LOST;
		}
		tp->lost_out = 0;
		tcp_clear_all_retrans_hints(tp);
	}

	if (tp->prior_ssthresh) { // 根据前一个慢启动阈值的旧值是否存在来判断是否撤销操作
		const struct inet_connection_sock *icsk = inet_csk(sk);

		tp->snd_cwnd = icsk->icsk_ca_ops->undo_cwnd(sk); // 调用拥塞算法的undo_cwnd方法

		if (tp->prior_ssthresh > tp->snd_ssthresh) {
			tp->snd_ssthresh = tp->prior_ssthresh; // 恢复到出现 recovery 状态时 的ssh_thresh
			tcp_ecn_withdraw_cwr(tp);              // 取消 TCP_ECN_DEMAND_CWR
		}
	}
	tp->snd_cwnd_stamp = tcp_jiffies32; // 记录最近一次检测cwnd 的时间
	tp->undo_marker = 0;   /* 复位撤销标志 */
	tp->rack.advanced = 1; /* Force RACK to re-exam losses */
}

static inline bool tcp_may_undo(const struct tcp_sock *tp)
{
    // undo_marker表明套接口进入了拥塞状态（TCP_CA_Recovery/TCP_CA_Loss），调整了拥塞窗口
    // 否则没有必要进行恢复窗口操作。并且需要满足以下条件中的一个：
    // 1.undo_retrans等于0. 报文重传之后被D-SACK确认，表明这些重传为不必要的，原始报文未丢失。
    // 2.retrans_stamp等于0（重传报文时间戳retrans_stamp等于零）. 在进入拥塞状态后还没有进行过任何重传，或者重传报文都已送达。
    // 3.接收到的ACK确认报文中的回复时间戳（rcv_tsecr）在重传报文的时间戳之前，表明是对于原始报文的确认，而不是对重传报文。
	return tp->undo_marker && (!tp->undo_retrans || tcp_packet_delayed(tp));
}

/* People celebrate: "We love our President!" */
static bool tcp_try_undo_recovery(struct sock *sk)
{
    tcp_sock *tp = tcp_sk(sk);

	if (tcp_may_undo(tp)) { // 确认是否需要恢复拥塞窗口
		int mib_idx;

		/* Happy end! We did not retransmit anything
		 * or our original transmission succeeded.
		 */
		DBGUNDO(sk, inet_csk(sk)->icsk_ca_state == TCP_CA_Loss ? "loss" : "retrans");
		tcp_undo_cwnd_reduction(sk, false); // 拥塞窗口恢复
		if (inet_csk(sk)->icsk_ca_state == TCP_CA_Loss)
			mib_idx = LINUX_MIB_TCPLOSSUNDO;
		else
			mib_idx = LINUX_MIB_TCPFULLUNDO;

		NET_INC_STATS(sock_net(sk), mib_idx);
	} else if (tp->rack.reo_wnd_persist) {
		tp->rack.reo_wnd_persist--;
	}
	if (tp->snd_una == tp->high_seq && tcp_is_reno(tp)) {
	    /*
	     * 对于Reno算法，如果当前窗口中还有重传报文存在于网络中，保留retrans_stamp的值，
	     * 避免这些重传报文触发dupack，再次引起错误的快速重传，此时需要保持拥塞状态不撤销，
	     * 当再次接收到新的ACK报文(tcp_try_undo_recovery再次运行，但不会再执行以上的撤销拥塞窗口部分),
	     * 确认SND.UNA大于high_seq后，进入TCP_CA_Open状态。
	     */
		/* Hold old state until something *above* high_seq
		 * is ACKed. For Reno it is MUST to prevent false
		 * fast retransmits (RFC2582). SACK TCP is safe. */
		if (!tcp_any_retrans_done(sk))
			tp->retrans_stamp = 0;
		return true;
	}
	// SND.UNA大于high_seq，套接口直接恢复到TCP_CA_Open状态。
	tcp_set_ca_state(sk, TCP_CA_Open);
    // 清空SACK Reneging标志
	tp->is_sack_reneg = 0;
	return false;
}

/* Try to undo cwnd reduction, because D-SACKs acked all retransmitted data */
static bool tcp_try_undo_dsack(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (tp->undo_marker && !tp->undo_retrans) {
	    // 如果undo_marker有值，并且undo_retrans为零，
	    // 表明所有的重传报文都被D-SACK所确认，即重传是不必要的，执行拥塞窗口恢复操作
		tp->rack.reo_wnd_persist = min(TCP_RACK_RECOVERY_THRESH,
					       tp->rack.reo_wnd_persist + 1);
		DBGUNDO(sk, "D-SACK");
		tcp_undo_cwnd_reduction(sk, false);
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPDSACKUNDO);
		return true;
	}
	return false;
}

/* Undo during loss recovery after partial ACK or using F-RTO. */
static bool tcp_try_undo_loss(struct sock *sk, bool frto_undo)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (frto_undo || tcp_may_undo(tp)) {   // FRTO执行撤销操作，或者tcp_may_undo检测到需要执行撤销
		tcp_undo_cwnd_reduction(sk, true); // 恢复拥塞窗口

		DBGUNDO(sk, "partial loss");
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPLOSSUNDO);
		if (frto_undo)
			NET_INC_STATS(sock_net(sk),
					LINUX_MIB_TCPSPURIOUSRTOS);
		inet_csk(sk)->icsk_retransmits = 0;
		if (frto_undo || tcp_is_sack(tp)) {
			tcp_set_ca_state(sk, TCP_CA_Open);
			tp->is_sack_reneg = 0; // 清空SACK Reneging标志
		}
		return true;
	}
	return false;
}

/* The cwnd reduction in CWR and Recovery uses the PRR algorithm in RFC 6937.
 * It computes the number of packets to send (sndcnt) based on packets newly
 * delivered:
 *   1) If the packets in flight is larger than ssthresh, PRR spreads the
 *	cwnd reductions across a full RTT.
 *   2) Otherwise PRR uses packet conservation to send as much as delivered.
 *      But when the retransmits are acked without further losses, PRR
 *      slow starts cwnd up to ssthresh to speed up the recovery.
 */
static void tcp_init_cwnd_reduction(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tp->high_seq = tp->snd_nxt;
	tp->tlp_high_seq = 0;
	tp->snd_cwnd_cnt = 0;
	tp->prior_cwnd = tp->snd_cwnd;
	tp->prr_delivered = 0;
	tp->prr_out = 0;
	tp->snd_ssthresh = inet_csk(sk)->icsk_ca_ops->ssthresh(sk); // 计算发送阈值
	tcp_ecn_queue_cwr(tp); // 添加CWR标志
}

void tcp_cwnd_reduction(struct sock *sk, int newly_acked_sacked, int flag)
{
	struct tcp_sock *tp = tcp_sk(sk);
	int sndcnt = 0;
	int delta = tp->snd_ssthresh - tcp_packets_in_flight(tp);

	if (newly_acked_sacked <= 0 || WARN_ON_ONCE(!tp->prior_cwnd))
		return;

	tp->prr_delivered += newly_acked_sacked;
	if (delta < 0) {
		u64 dividend = (u64)tp->snd_ssthresh * tp->prr_delivered +
			       tp->prior_cwnd - 1;
		sndcnt = div_u64(dividend, tp->prior_cwnd) - tp->prr_out;
	} else if ((flag & (FLAG_RETRANS_DATA_ACKED | FLAG_LOST_RETRANS)) ==
		   FLAG_RETRANS_DATA_ACKED) {
		sndcnt = min_t(int, delta,
			       max_t(int, tp->prr_delivered - tp->prr_out,
				     newly_acked_sacked) + 1);
	} else {
		sndcnt = min(delta, newly_acked_sacked);
	}
	/* Force a fast retransmit upon entering fast recovery */
	sndcnt = max(sndcnt, (tp->prr_out ? 0 : 1));
	tp->snd_cwnd = tcp_packets_in_flight(tp) + sndcnt;
}

static inline void tcp_end_cwnd_reduction(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (inet_csk(sk)->icsk_ca_ops->cong_control)
		return;

	/* Reset cwnd to ssthresh in CWR or Recovery (unless it's undone) */
	if (tp->snd_ssthresh < TCP_INFINITE_SSTHRESH &&
	    (inet_csk(sk)->icsk_ca_state == TCP_CA_CWR || tp->undo_marker)) {
		tp->snd_cwnd = tp->snd_ssthresh;
		tp->snd_cwnd_stamp = tcp_jiffies32;
	}
	tcp_ca_event(sk, CA_EVENT_COMPLETE_CWR);
}

/* Enter CWR state. Disable cwnd undo since congestion is proven with ECN */
void tcp_enter_cwr(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tp->prior_ssthresh = 0; // 重新设置慢启动阈值
	if (inet_csk(sk)->icsk_ca_state < TCP_CA_CWR) {
		tp->undo_marker = 0; // 清除undo需要的标志，不允许undo
		tcp_init_cwnd_reduction(sk);
		tcp_set_ca_state(sk, TCP_CA_CWR); // 设置此时的状态为TCP_CA_CWR
	}
}
EXPORT_SYMBOL(tcp_enter_cwr);

static void tcp_try_keep_open(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	int state = TCP_CA_Open;

	if (tcp_left_out(tp) || tcp_any_retrans_done(sk))
	    // 套接口还有乱序报文或者丢失报文 进入disorder状态
		state = TCP_CA_Disorder;

	if (inet_csk(sk)->icsk_ca_state != state) {
		tcp_set_ca_state(sk, state);
		tp->high_seq = tp->snd_nxt;
	}
}

static void tcp_try_to_open(struct sock *sk, int flag)
{
	struct tcp_sock *tp = tcp_sk(sk);

	tcp_verify_left_out(tp);

	if (!tcp_any_retrans_done(sk))
		tp->retrans_stamp = 0;

	if (flag & FLAG_ECE)
		tcp_enter_cwr(sk);

	if (inet_csk(sk)->icsk_ca_state != TCP_CA_CWR) {
		tcp_try_keep_open(sk);
	}
}

static void tcp_mtup_probe_failed(struct sock *sk)
{
	struct inet_connection_sock *icsk = inet_csk(sk);

	icsk->icsk_mtup.search_high = icsk->icsk_mtup.probe_size - 1;
	icsk->icsk_mtup.probe_size = 0;
	NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPMTUPFAIL);
}

static void tcp_mtup_probe_success(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct inet_connection_sock *icsk = inet_csk(sk);

	/* FIXME: breaks with very large cwnd */
	tp->prior_ssthresh = tcp_current_ssthresh(sk);
	tp->snd_cwnd = tp->snd_cwnd *
		       tcp_mss_to_mtu(sk, tp->mss_cache) /
		       icsk->icsk_mtup.probe_size;
	tp->snd_cwnd_cnt = 0;
	tp->snd_cwnd_stamp = tcp_jiffies32;
	tp->snd_ssthresh = tcp_current_ssthresh(sk);

	icsk->icsk_mtup.search_low = icsk->icsk_mtup.probe_size;
	icsk->icsk_mtup.probe_size = 0;
	tcp_sync_mss(sk, icsk->icsk_pmtu_cookie);
	NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPMTUPSUCCESS);
}

/* Do a simple retransmit without using the backoff mechanisms in
 * tcp_timer. This is used for path mtu discovery.
 * The socket is already locked here.
 */
void tcp_simple_retransmit(struct sock *sk)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *skb;
	unsigned int mss = tcp_current_mss(sk);

	skb_rbtree_walk(skb, &sk->tcp_rtx_queue) {
		if (tcp_skb_seglen(skb) > mss &&
		    !(TCP_SKB_CB(skb)->sacked & TCPCB_SACKED_ACKED)) {
			if (TCP_SKB_CB(skb)->sacked & TCPCB_SACKED_RETRANS) {
				TCP_SKB_CB(skb)->sacked &= ~TCPCB_SACKED_RETRANS;
				tp->retrans_out -= tcp_skb_pcount(skb);
			}
			tcp_skb_mark_lost_uncond_verify(tp, skb);
		}
	}

	tcp_clear_retrans_hints_partial(tp);

	if (!tp->lost_out)
		return;

	if (tcp_is_reno(tp))
		tcp_limit_reno_sacked(tp);

	tcp_verify_left_out(tp);

	/* Don't muck with the congestion window here.
	 * Reason is that we do not increase amount of _data_
	 * in network, but units changed and effective
	 * cwnd/ssthresh really reduced now.
	 */
	if (icsk->icsk_ca_state != TCP_CA_Loss) {
		tp->high_seq = tp->snd_nxt;
		tp->snd_ssthresh = tcp_current_ssthresh(sk);
		tp->prior_ssthresh = 0;
		tp->undo_marker = 0;
		tcp_set_ca_state(sk, TCP_CA_Loss);
	}
	tcp_xmit_retransmit_queue(sk);
}
EXPORT_SYMBOL(tcp_simple_retransmit);

void tcp_enter_recovery(struct sock *sk, bool ece_ack)
{
	struct tcp_sock *tp = tcp_sk(sk);
	int mib_idx;

	if (tcp_is_reno(tp))
		mib_idx = LINUX_MIB_TCPRENORECOVERY;
	else
		mib_idx = LINUX_MIB_TCPSACKRECOVERY;

	NET_INC_STATS(sock_net(sk), mib_idx);

	tp->prior_ssthresh = 0;
	tcp_init_undo(tp);

	if (!tcp_in_cwnd_reduction(sk)) {
		if (!ece_ack)
			tp->prior_ssthresh = tcp_current_ssthresh(sk);
		tcp_init_cwnd_reduction(sk);
	}
	tcp_set_ca_state(sk, TCP_CA_Recovery);
}

/* Process an ACK in CA_Loss state. Move to CA_Open if lost data are
 * recovered or spurious. Otherwise retransmits more on partial ACKs.
 */
// 如果ACK报文推进了SND.UNA序号，尝试进行TCP_CA_Loss状态撤销，由函数tcp_try_undo_loss完成。
// 对于FRTO，如果S/ACK确认了并没有重传的报文（原始报文），同样尝试进入撤销流程，
// 因为此ACK报文表明RTO值设置的不够长（并非拥塞导致报文丢失），过早进入了TCP_CA_Loss状态。
static void tcp_process_loss(struct sock *sk, int flag, int num_dupack,
			     int *rexmit)
{
	struct tcp_sock *tp = tcp_sk(sk);
	bool recovered = !before(tp->snd_una, tp->high_seq);// SND.UNA不在high_seq之前，表明完全恢复

    // 最大的未确认包已经发生改变，可能是之前丢包已经恢复，尝试撤销丢包状态。
    // 当frto关闭时，这是唯二可以退出LOSS状态的条件。
	if ((flag & FLAG_SND_UNA_ADVANCED || rcu_access_pointer(tp->fastopen_rsk)) &&
	    tcp_try_undo_loss(sk, false)) // 如果ACK报文推进了SND.UNA序号，尝试使用tcp_try_undo_loss进行TCP_CA_Loss状态撤销
		return;

	if (tp->frto) { /* F-RTO RFC5682 sec 3.1 (sack enhanced version). */
		/* Step 3.b. A timeout is spurious if not all data are
		 * lost, i.e., never-retransmitted data are (s)acked.
		 * /
		 /* #define FLAG_ORIG_SACK_ACKED 0x200 /* Never retransmitted data are (s)acked  */
		 /* 如果S/ACK确认了并没有重传的报文（原始报文），只是延迟了，这是虚假RTO，同样尝试进入撤销流程，
		  * 因为此ACK报文表明RTO值设置的不够长（并非拥塞导致报文丢失），过早进入了TCP_CA_Loss状态
		  * 注: 这里的frto_undo传参为true，必定恢复。
		  * 对应RTO论文图中的延迟包的acks。
		  */
		if ((flag & FLAG_ORIG_SACK_ACKED) && // high_seq之前的非重传的数据被ack/sack
		    tcp_try_undo_loss(sk, true)) // 认为上次超时是spurious的，undo
			return;

        // 走到这里表明  ----重传数据被ack/sack或者新发送的数据sack， 或者reno收到dupack
		if (after(tp->snd_nxt, tp->high_seq)) { // 有新数据发送，说明是f-rto算法的第2个ack
            // 如果是刚进入LOSS状态，会先尝试重传，这时候snd_nxt总是等于high_seq的，
            // 这个分支主要对应3.2.b之后发送了两个新分片。
            // 虽然发送了新分片，没有发重传，但是这时候收到的ack并没有更新una
            // 说明这个rtt中，之前una的包仍旧没有达到，因此这里认为他是真的超时
            // 关闭frto。对应3.3.a
		    if (flag & FLAG_DATA_SACKED || num_dupack)
				tp->frto = 0; /* Step 3.a. loss was real */ /* loss 状态是真的 不是误判 */
		} else if (flag & FLAG_SND_UNA_ADVANCED && !recovered) { // 窗口移动, 但high_seq没有全部确认
            // 这里进入的条件为
            // 1. snd_nxt == high_seq，还没发送过新分片
            // 2. una更新过，且没有完全恢复
            // 执行3.2.b，发送新分片。
            // 对应论文图中收到了一个更新过snd_una的ack。
		    tp->high_seq = tp->snd_nxt;
			/* Step 2.b. Try send new data (but deferred until cwnd
			 * is updated in tcp_ack()). Otherwise fall back to
			 * the conventional recovery.
			 */
			if (!tcp_write_queue_empty(sk) &&
			    after(tcp_wnd_end(tp), tp->snd_nxt)) {
				*rexmit = REXMIT_NEW; // 标记发送新数据，会在tcp_xmit_recovery中处理
				return;
			}
			tp->frto = 0;
		}
	}

    // snd_una > high_seq
    // 已经完全恢复，则撤销对应的恢复操作，并进入TCP_CA_OPEN状态。后续将进入恢复状态。
    // 这里主要处理了其他几个不在FRTO可处理的场景，如3.2.a和3.3.a
    // 唯一进入这里但frto还可能生效的场景为:
    // 发送新分片后，但是收到了一个不是新的sack，且不是一个dup sack。
    // 在这种情况下的处理应该和上一个旧的sack相同。

	if (recovered) { // 为此ACK报文表明RTO值设置的不够长（并非拥塞导致报文丢失），过早进入了TCP_CA_Loss状态。
	    // 如果SND.UNA不在high_seq之前，表明恢复流程已经结束，
	    // 进入TCP_CA_Loss状态时的发送报文（SND.NXT（high_seq））都已经被确认，
	    // 执行tcp_try_undo_recovery。
		/* F-RTO RFC5682 sec 3.1 step 2.a and 1st part of step 3.a */
		tcp_try_undo_recovery(sk);
		return;
	}

    // snd_una < high_seq， 进入loss前发送的包没有全部确认

	if (tcp_is_reno(tp)) {
		/* A Reno DUPACK means new data in F-RTO step 2.b above are
		 * delivered. Lower inflight to clock out (re)tranmissions.
		 */
		if (after(tp->snd_nxt, tp->high_seq) && num_dupack) // snd_nxt > high_seq很可能是frto中发送的新数据被dupack
			tcp_add_reno_sack(sk, num_dupack); // 旧dupack，减少inflight包数量，从而减少重传包
		else if (flag & FLAG_SND_UNA_ADVANCED) // 本次窗口更新 una 在增长
			tcp_reset_reno_sack(tp); // 因为reno只会重传第一个包，窗口滑动reno就可以重置了
	}
	*rexmit = REXMIT_LOST; // 标记发送重传队列中的数据，会在tcp_xmit_recovery中处理
}

/* Undo during fast recovery after partial ACK. */
/*
 * 与tcp_try_undo_recovery函数不同，这里没有使用tcp_may_undo进行撤销拥塞窗口的判断，
 * 而是使用了其中的一部分，即tcp_packet_delayed判断报文是否仅是被延迟了，忽略undo_retrans值的判断。
 * 其逻辑是在接收到部分确认ACK的情况下，只要tcp_packet_delayed成立，原始报文就没有丢失而是被延时了，
 * 就应检查当前的乱序级别设置是否需要更新（tcp_check_sack_reordering），防止快速重传被误触发。
 */
static bool tcp_try_undo_partial(struct sock *sk, u32 prior_snd_una)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (tp->undo_marker && tcp_packet_delayed(tp)) {
		/* Plain luck! Hole if filled with delayed
		 * packet, rather than with a retransmit. Check reordering.
		 */
		tcp_check_sack_reordering(sk, prior_snd_una, 1);

		/* We are getting evidence that the reordering degree is higher
		 * than we realized. If there are no retransmits out then we
		 * can undo. Otherwise we clock out new packets but do not
		 * mark more packets lost or retransmit more.
		 */
		if (tp->retrans_out) // 网络中还有发出的重传报文，不进行拥塞窗口的撤销操作
			return true;

		if (!tcp_any_retrans_done(sk))
		    // 变量retrans_stamp记录了第一个重传报文的时间戳，
		    // 如果已经没有了重传报文，清零此时间戳
			tp->retrans_stamp = 0;

		DBGUNDO(sk, "partial recovery");
        // 网络中没有重传的报文or发送skb缓存中没有报文是被重传过
        // 则取消所有报文lost状态以及调整拥塞窗口阈值等
		tcp_undo_cwnd_reduction(sk, true);
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPPARTIALUNDO);
		tcp_try_keep_open(sk); // 尝试进入TCP_CA_Open状态
		return true;
	}
	return false;
}

static void tcp_identify_packet_loss(struct sock *sk, int *ack_flag)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (tcp_rtx_queue_empty(sk))
		return;

	if (unlikely(tcp_is_reno(tp))) { // 对于Reno/NewReno-TCP
		tcp_newreno_mark_lost(sk, *ack_flag & FLAG_SND_UNA_ADVANCED);
	} else if (tcp_is_rack(sk)) { // 对于启用RACK算法的TCP，由函数tcp_rack_mark_lost标记丢包
		u32 prior_retrans = tp->retrans_out;

		tcp_rack_mark_lost(sk);
		if (prior_retrans > tp->retrans_out) // 之前的重传报文数量大于当前的重传数量,表明丢失了部分重传报文
			*ack_flag |= FLAG_LOST_RETRANS;  // 设置FLAG_LOST_RETRANS标志
	}
}

static bool tcp_force_fast_retransmit(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	return after(tcp_highest_sack_seq(tp),
		     tp->snd_una + tp->reordering * tp->mss_cache);
}

/* Process an event, which can update packets-in-flight not trivially.
 * Main goal of this function is to calculate new estimate for left_out,
 * taking into account both packets sitting in receiver's buffer and
 * packets lost by network.
 *
 * Besides that it updates the congestion state when packet loss or ECN
 * is detected. But it does not reduce the cwnd, it is done by the
 * congestion control later.
 *
 * It does _not_ decide what to send, it is made in function
 * tcp_xmit_retransmit_queue().
 */
*/
/* FACK的全称是forward acknowledgement，FACK通过记录SACK块中系列号最大(forward-most)的SACK块来推测丢包信息，
 * 在linux中使用fackets_out这个状态变量来记录FACK信息。
 * 我们之前介绍SACK重传时候说过在SACK下需要3个dup ACK来触发快速重传(3个为默认值)，
 * 而SACK下的dup ACK的定义与传统的非SACK下定义又略有不同(详细请参考前面的文章和示例)。
 * 当使能FACK的时候，实际上我们可以通过一个SACK块信息来推测丢包情况进而触发快速重传。
 * 比如server端依次发出P1(0-9)、P2(10-19)、P3(20-29)、P4(30-39)、P5(40-49)，
 * 假设client端正常收到了P1包并回复了ACK确认包，P2、P3、P4则由于网络拥塞等原因丢失，
 * client在收到P5时候回复一个Ack=10的确认包，并携带P5有SACK块信息(40-50)，
 * 这样server在收到P1的确认包和P5的dup ACK时候，就可以根据dup ACK中的SACK信息得知client端收到了P1报文和P5报文，
 * 计算出P1和P5两个数据包中间间隔了3个数据包，达到了dup ACK门限(默认为3)，进而推测出P2报文丢失。
*/
static void tcp_fastretrans_alert(struct sock *sk, const u32 prior_snd_una,
				  int num_dupack, int *ack_flag, int *rexmit)
{
	struct inet_connection_sock *icsk = inet_csk(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	int fast_rexmit = 0, flag = *ack_flag;
	// 接收到dupack，或者对端SACK序号块确认的最高序号，超出SND.UNA加上乱序级别的值，认为套接口发生了丢包
	bool do_lost = num_dupack || ((flag & FLAG_DATA_SACKED) && // 新来的一个sack
				      tcp_force_fast_retransmit(sk)); // 是否启动快速重传

    /* 如果packet_out 等待被ack的报文为0，那么不可能有sacked_out（被sack 确认的段） */
	if (!tp->packets_out && tp->sacked_out)
		tp->sacked_out = 0;

	/* Now state machine starts.
	 * A. ECE, hence prohibit cwnd undoing, the reduction is required. */
	/* 禁止拥塞窗口撤销，并开始减小拥塞窗口 */
	if (flag & FLAG_ECE)
		tp->prior_ssthresh = 0;

	/* B. In all the states check for reneging SACKs. */
	/*
	 * 检查是否为虚假的SACK，即ACK是否确认已经被SACK的数据
	 * 如果接收到的 ACK 指向已记录的 SACK，这说明我们记录的 SACK 并没有反应接收方的真实状态。
	 * 也就是说接收方现在已经处于严重的拥塞状态或者在处理上有bug，那么我们接下来就要按照重传超时的方式去处理。
	 * 因为按照正常的逻辑流程，接受的 ACK不应该指向已记录的 SACK，而应指向 SACK 并未包含的，
	 * 这说明接收方由于拥塞已经把 SACK 部分接收的段已经丢弃或者处理上有 BUG，我们必须需要重传
     */
	if (tcp_check_sack_reneging(sk, flag))
		return;

	/* C. Check consistency of the current state. */
	/* 查看是否从发送队列发出的包的数量是否不小于发出主机的包的数量
	 * 该函数的功能主要是判断 left_out 是否大于 packets_out, 当然，这是不可能的，
	 * 因为前者是已经发送离开主机的未被确认的段数，而后者是已经离开发送队列 (不一定离开主机)但未确认的段数。
	 * 故而，这里有一个WARN_ON，以便输出相应的警告信息
	 */
	tcp_verify_left_out(tp);

	/* D. Check state exit conditions. State can be terminated
	 *    when high_seq is ACKed. */
	if (icsk->icsk_ca_state == TCP_CA_Open) {
		WARN_ON(tp->retrans_out != 0);
		tp->retrans_stamp = 0; /* 清除上次重传阶段第一个重传段的发送时间*/
	} else if (!before(tp->snd_una, tp->high_seq)) {
		switch (icsk->icsk_ca_state) {
		case TCP_CA_CWR:
			/* CWR is to be held something *above* high_seq
			 * is ACKed for CWR bit to reach receiver. */
			if (tp->snd_una != tp->high_seq) { // 第一个if 是 >= 现在只需要判断 > 就行
				tcp_end_cwnd_reduction(sk);    // 需要snd_una > high_seq才能撤销---结束窗口减小
				tcp_set_ca_state(sk, TCP_CA_Open); // 回到 OPen 状态
			}
			break;

		case TCP_CA_Recovery:
		    // ack_seq序号确认了high_seq之前的所有报文（SND.UNA >= high_seq），如上节所述，
		    // high_seq记录了进入拥塞时的最大发送序号SND.NXT，故表明对端接收到了SND.NXT之前的所有报文，
		    // 未发生丢包，需要撤销拥塞状态，由函数tcp_try_undo_recovery实现。
            /* TCP_CA_Recovery拥塞状态接收到ACK报文，
             * 其ack_seq序号确认了high_seq之前的所有报文（SND.UNA >= high_seq），
             * high_seq记录了进入拥塞时的最大发送序号SND.NXT，
             * 故表明对端接收到了SND.NXT之前的所有报文，未发生丢包，需要撤销拥塞状态
             * */
			if (tcp_is_reno(tp)) // 判断对方是否提供了 SACK 服务，提供，返回 0, 否则返回 1
				tcp_reset_reno_sack(tp); // 设置 sacked_out 为 0
			if (tcp_try_undo_recovery(sk)) // 尝试从 Recovery 状态撤销 成功，就直接返回
				return;
			tcp_end_cwnd_reduction(sk); // 结束拥塞窗口缩小
			break;
		}
	}

	/* E. Process state. */
	switch (icsk->icsk_ca_state) {
	case TCP_CA_Recovery:

		if (!(flag & FLAG_SND_UNA_ADVANCED)) { // 接收到的ACK报文（dupack）未能推进SND.UNA
			if (tcp_is_reno(tp))
				tcp_add_reno_sack(sk, num_dupack);
		} else {
            /*
             * 未能施行拥塞撤销操作（报文确实已经丢失），
             * 参见函数tcp_try_undo_partial（接收到对原始报文的确认）
             * 和tcp_try_undo_dsack（全部重传被DSACK确认）。进行丢包标记
             */
            /*
             * ACK报文没有确认全部的进入拥塞时SND.NXT（high_seq）之前的数据，
             * 仅确认了一部分（FLAG_SND_UNA_ADVANCED）
             */
			if (tcp_try_undo_partial(sk, prior_snd_una))
				return;
			/* Partial ACK arrived. Force fast retransmit. */
			do_lost = tcp_force_fast_retransmit(sk);
		}
		if (tcp_try_undo_dsack(sk)) { // ACK报文并没有推进SND.UNA序号，或者在partial-undo未执行的情况下，尝试进行DSACK相关的撤销操作
			tcp_try_keep_open(sk);
			return;
		}
		tcp_identify_packet_loss(sk, ack_flag); // 丢包标记
		break;
	case TCP_CA_Loss:
		tcp_process_loss(sk, flag, num_dupack, rexmit); // 未能执行拥塞撤销（恢复到TCP_CA_Open）
		tcp_identify_packet_loss(sk, ack_flag);
		if (!(icsk->icsk_ca_state == TCP_CA_Open ||
		      (*ack_flag & FLAG_LOST_RETRANS)))
			return;
		/* Change state if cwnd is undone or retransmits are lost */
		fallthrough;
	default:
	    // 套接口的拥塞状态不等于TCP_CA_Recovery也不等于TCP_CA_Loss，
	    // 在tcp_time_to_recover函数检测到需要进行快速恢复时，
	    // 设置fast_rexmit变量为真。
		if (tcp_is_reno(tp)) {
			if (flag & FLAG_SND_UNA_ADVANCED)
				tcp_reset_reno_sack(tp);
			tcp_add_reno_sack(sk, num_dupack);
		}

		if (icsk->icsk_ca_state <= TCP_CA_Disorder)
			tcp_try_undo_dsack(sk);

		tcp_identify_packet_loss(sk, ack_flag); // 丢包标记
		// 确定能够离开 Disorder 状态，而进入 Recovery 状态。
		// 如果不进入 Recovery 状态，判断可否进入 OPen 状态。
		if (!tcp_time_to_recover(sk, flag)) { // 依据丢包或者dupack/sack数量来判断是否进入快速恢复阶段
			tcp_try_to_open(sk, flag); // 如果不进入 Recovery 状态，判断可否进入 OPen 状态。
			return;
		}

		/* MTU probe failure: don't reduce cwnd */
		if (icsk->icsk_ca_state < TCP_CA_CWR &&
		    icsk->icsk_mtup.probe_size &&
		    tp->snd_una == tp->mtu_probe.probe_seq_start) {
			tcp_mtup_probe_failed(sk);
			/* Restores the reduction we did in tcp_mtup_probe() */
			tp->snd_cwnd++;
			tcp_simple_retransmit(sk);
			return;
		}

		/* Otherwise enter Recovery state */
		tcp_enter_recovery(sk, (flag & FLAG_ECE)); // lost_out有值，进入TCP_CA_Recovery拥塞状态，重传丢失报文（REXMIT_LOST）。
		fast_rexmit = 1;
	}

	if (!tcp_is_rack(sk) && do_lost)
	    /* 对于未启用RACK算法的情况，判断发生丢包。前提：未能施行拥塞撤销操作（报文确实已经丢失），
         * 即函数tcp_try_undo_partial（接收到对原始报文的确认和tcp_try_undo_dsack（全部重传被DSACK确认）
         * 都操作失败。而且非rack和非Reno/NewReno
         */
		tcp_update_scoreboard(sk, fast_rexmit); /* 更新记分牌，标志丢失和超时的数据包，增加lost_out */
	*rexmit = REXMIT_LOST;
}

static void tcp_update_rtt_min(struct sock *sk, u32 rtt_us, const int flag)
{
	u32 wlen = sock_net(sk)->ipv4.sysctl_tcp_min_rtt_wlen * HZ;
	struct tcp_sock *tp = tcp_sk(sk);

	if ((flag & FLAG_ACK_MAYBE_DELAYED) && rtt_us > tcp_min_rtt(tp)) {
		/* If the remote keeps returning delayed ACKs, eventually
		 * the min filter would pick it up and overestimate the
		 * prop. delay when it expires. Skip suspected delayed ACKs.
		 */
		return;
	}
	minmax_running_min(&tp->rtt_min, wlen, tcp_jiffies32,
			   rtt_us ? : jiffies_to_usecs(1));
}

static bool tcp_ack_update_rtt(struct sock *sk, const int flag,
			       long seq_rtt_us, long sack_rtt_us,
			       long ca_rtt_us, struct rate_sample *rs)
{
	const struct tcp_sock *tp = tcp_sk(sk);

	/* Prefer RTT measured from ACK's timing to TS-ECR. This is because
	 * broken middle-boxes or peers may corrupt TS-ECR fields. But
	 * Karn's algorithm forbids taking RTT if some retransmitted data
	 * is acked (RFC6298).
	 */
	if (seq_rtt_us < 0)
		seq_rtt_us = sack_rtt_us;

	/* RTTM Rule: A TSecr value received in a segment is used to
	 * update the averaged RTT measurement only if the segment
	 * acknowledges some new data, i.e., only if it advances the
	 * left edge of the send window.
	 * See draft-ietf-tcplw-high-performance-00, section 3.3.
	 */
	if (seq_rtt_us < 0 && tp->rx_opt.saw_tstamp && tp->rx_opt.rcv_tsecr &&
	    flag & FLAG_ACKED) {
		u32 delta = tcp_time_stamp(tp) - tp->rx_opt.rcv_tsecr;

		if (likely(delta < INT_MAX / (USEC_PER_SEC / TCP_TS_HZ))) {
			seq_rtt_us = delta * (USEC_PER_SEC / TCP_TS_HZ);
			ca_rtt_us = seq_rtt_us;
		}
	}
	rs->rtt_us = ca_rtt_us; /* RTT of last (S)ACKed packet (or -1) */
	if (seq_rtt_us < 0)
		return false;

	/* ca_rtt_us >= 0 is counting on the invariant that ca_rtt_us is
	 * always taken together with ACK, SACK, or TS-opts. Any negative
	 * values will be skipped with the seq_rtt_us < 0 check above.
	 */
	tcp_update_rtt_min(sk, ca_rtt_us, flag);
	tcp_rtt_estimator(sk, seq_rtt_us);
	tcp_set_rto(sk);

	/* RFC6298: only reset backoff on valid RTT measurement. */
	inet_csk(sk)->icsk_backoff = 0;
	return true;
}

/* Compute time elapsed between (last) SYNACK and the ACK completing 3WHS. */
void tcp_synack_rtt_meas(struct sock *sk, struct request_sock *req)
{
	struct rate_sample rs;
	long rtt_us = -1L;

	if (req && !req->num_retrans && tcp_rsk(req)->snt_synack)
		rtt_us = tcp_stamp_us_delta(tcp_clock_us(), tcp_rsk(req)->snt_synack);

	tcp_ack_update_rtt(sk, FLAG_SYN_ACKED, rtt_us, -1L, rtt_us, &rs);
}


static void tcp_cong_avoid(struct sock *sk, u32 ack, u32 acked)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);

	icsk->icsk_ca_ops->cong_avoid(sk, ack, acked);
	tcp_sk(sk)->snd_cwnd_stamp = tcp_jiffies32;
}

/* Restart timer after forward progress on connection.
 * RFC2988 recommends to restart timer to now+rto.
 */
void tcp_rearm_rto(struct sock *sk)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	/* If the retrans timer is currently being used by Fast Open
	 * for SYN-ACK retrans purpose, stay put.
	 */
	if (rcu_access_pointer(tp->fastopen_rsk))
		return;

	if (!tp->packets_out) { // 网络中没有已发送的数据
	    // 清除定时器
		inet_csk_clear_xmit_timer(sk, ICSK_TIME_RETRANS);
	} else {
        // 重新安装retrans定时器，走到这里，说明packet_out不为0。
        // 如果TLP探测报文未能发送，但是TLP定时器已经消耗了一定的时间，重新计算此时RTO超时的剩余时间。
        // 否则如果TLP探测报文发送完成，启动一个完整时长的RTO定时器。
		u32 rto = inet_csk(sk)->icsk_rto;
		/* Offset the time elapsed after installing regular RTO */
		if (icsk->icsk_pending == ICSK_TIME_REO_TIMEOUT ||
		    icsk->icsk_pending == ICSK_TIME_LOSS_PROBE) {
			s64 delta_us = tcp_rto_delta_us(sk);
			/* delta_us may not be positive if the socket is locked
			 * when the retrans timer fires and is rescheduled.
			 */
			rto = usecs_to_jiffies(max_t(int, delta_us, 1));
		}
		// 重置定时器
		tcp_reset_xmit_timer(sk, ICSK_TIME_RETRANS, rto,
				     TCP_RTO_MAX);
	}
}

/* Try to schedule a loss probe; if that doesn't work, then schedule an RTO. */
static void tcp_set_xmit_timer(struct sock *sk)
{
	if (!tcp_schedule_loss_probe(sk, true)) /* 返回false代表未设置timer, 返回true代表设置了PTO timer */
		tcp_rearm_rto(sk);
}

/* If we get here, the whole TSO packet has not been acked. */
// TSO 包并没有全部被确认，现在需要统计已经被确认的数量
static u32 tcp_tso_acked(struct sock *sk, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 packets_acked;

    // seq---end_seq---snd_una  这种情况不可能进来
	BUG_ON(!after(TCP_SKB_CB(skb)->end_seq, tp->snd_una));

	packets_acked = tcp_skb_pcount(skb); // TSO段总共包括几个
	if (tcp_trim_head(sk, skb, tp->snd_una - TCP_SKB_CB(skb)->seq))
        // 对于已经确认的部分，更新skb中的信息。例如len之类信息都变了
        // 然后重新计算出新的剩余的segs
		return 0;
	packets_acked -= tcp_skb_pcount(skb); // 之前总的segs - 现在剩余的segs == 被确认的segs

	if (packets_acked) {
		BUG_ON(tcp_skb_pcount(skb) == 0);
		BUG_ON(!before(TCP_SKB_CB(skb)->seq, TCP_SKB_CB(skb)->end_seq));
	}

	return packets_acked; // 返回被确认的数量
}

static void tcp_ack_tstamp(struct sock *sk, struct sk_buff *skb,
			   u32 prior_snd_una)
{
	const struct skb_shared_info *shinfo;

	/* Avoid cache line misses to get skb_shinfo() and shinfo->tx_flags */
	if (likely(!TCP_SKB_CB(skb)->txstamp_ack))
		return;

	shinfo = skb_shinfo(skb);
	if (!before(shinfo->tskey, prior_snd_una) &&
	    before(shinfo->tskey, tcp_sk(sk)->snd_una)) {
		tcp_skb_tsorted_save(skb) {
			__skb_tstamp_tx(skb, NULL, sk, SCM_TSTAMP_ACK);
		} tcp_skb_tsorted_restore(skb);
	}
}

/* Remove acknowledged frames from the retransmission queue. If our packet
 * is before the ack sequence we can discard it as it's confirmed to have
 * arrived at the other end.
 */
static int tcp_clean_rtx_queue(struct sock *sk, u32 prior_fack,
			       u32 prior_snd_una,
			       struct tcp_sacktag_state *sack)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);
	u64 first_ackt, last_ackt;
	struct tcp_sock *tp = tcp_sk(sk);
	u32 prior_sacked = tp->sacked_out; // 发送出去，还在网络上跑，但是还没有被确认的数据包们
	u32 reord = tp->snd_nxt; /* lowest acked un-retx un-sacked seq */
	struct sk_buff *skb, *next;
	bool fully_acked = true;
	long sack_rtt_us = -1L;
	long seq_rtt_us = -1L;
	long ca_rtt_us = -1L;
	u32 pkts_acked = 0;
	u32 last_in_flight = 0;
	bool rtt_update;
	int flag = 0;

	first_ackt = 0;

	for (skb = skb_rb_first(&sk->tcp_rtx_queue); skb; skb = next) {
		struct tcp_skb_cb *scb = TCP_SKB_CB(skb);
		const u32 start_seq = scb->seq;
		u8 sacked = scb->sacked;
		u32 acked_pcount;

		tcp_ack_tstamp(sk, skb, prior_snd_una);

		/* Determine how many packets and what bytes were acked, tso and else */
		/*
		 * 注意这个scb是我们发出去的数据的skb中的一个scb哦！，不是接受到的数据！小心
		 * 这里的意思就是发出去的数据最后一个字节在已经确认的snd_una之后，说明还有没有确认的字节
		 * 如果没有设置了TSO 或者 seq不在snd_una之前，即不是 seq---snd_una---end_seq这样情况
		 * 那么说明没有必要把重传元素去掉，(如果是seq---snd_una---end_seq)那么前面半部分的就可以
		 * 冲队列中删除！！！  注意是需要理解cb[]数组中seq和end_seq意义！在分片的情况下也是不变的！
		 */
		if (after(scb->end_seq, tp->snd_una)) {
            // 如果是大包那么tcp_gso_segs肯定不为1
            // UNA在skb起始序号之前
            // 上面两种情况都属于异常情况直接break终止报文处理，也即这种报文下载在处理
			if (tcp_skb_pcount(skb) == 1 ||
			    !after(tp->snd_una, scb->seq))
				break;

            // 如果只确认了TSO段中的一部分，则从skb删除已经确认的segs，并统计确认了多少段
            // 即是说大包的时候检查应答了多少个报文
			acked_pcount = tcp_tso_acked(sk, skb);
			if (!acked_pcount) // 处理出错
				break;
            // fully_acked表示SKB整包是否被应答
			fully_acked = false;
		} else {
            // 即 !after(scb->end_seq, tp->snd_una)，说明已经完全确认OK！
			acked_pcount = tcp_skb_pcount(skb);
		}

        // 下面通过sack的信息得到这是一个被重传的过包
        // 进入的话表示这个当前处理的SKB曾经被重传过
		if (unlikely(sacked & TCPCB_RETRANS)) {
            //并且是被SACK触发的重传
            // 如果之前重传过，&& 之前还没收到回复
			if (sacked & TCPCB_SACKED_RETRANS)
                // 现在需要更新重传的且没有收到ACK的包
				tp->retrans_out -= acked_pcount;
			flag |= FLAG_RETRANS_DATA_ACKED; // 重传包收到ACK
		} else if (!(sacked & TCPCB_SACKED_ACKED)) {// 当前ACK应答了没有被重传过的报文，也没不是被SACK应答，也即是正常ACK顺序应答
            //处理被正顺序应答的报文需要更新乱序数据包量统计reord和更新last_ackt
			last_ackt = tcp_skb_timestamp_us(skb);
			WARN_ON_ONCE(last_ackt == 0);
			if (!first_ackt)
				first_ackt = last_ackt;

			last_in_flight = TCP_SKB_CB(skb)->tx.in_flight;
			// 在清理重传队列时，如果其中的某个报文即没有被重传过，也没有被SACK确认过，
			// 而是直接由TCP头部的ACK字段所确认，更新reord乱序源头。
			// 如果此序号值小于在接收到此报文之前的最大SACK确认序号，表明发生了乱序。
			if (before(start_seq, reord))
				reord = start_seq;
			if (!after(scb->end_seq, tp->high_seq))
				flag |= FLAG_ORIG_SACK_ACKED;
		}

        // 如果是有sack标识
        // 当前处理的报文曾经是被SACK应大过
		if (sacked & TCPCB_SACKED_ACKED) {
            // 那么更新sack的发出没有接受到确认的数量
			tp->sacked_out -= acked_pcount;
		} else if (tcp_is_sack(tp)) {
			tp->delivered += acked_pcount;
            //没有打开TIMSTAMP,此处必然被执行
            //如果是sack应答数据不会更新rack.mstamp
			if (!tcp_skb_spurious_retrans(tp, skb))
				tcp_rack_advance(tp, sacked, scb->end_seq,
						 tcp_skb_timestamp_us(skb));
		}
        // 如果是丢包标识，那么更新数量
		if (sacked & TCPCB_LOST)
			tp->lost_out -= acked_pcount;

        // 发送的包没有确认的数量-=acked_pcount
		tp->packets_out -= acked_pcount;
        // 接收到确认的包数量+=acked_pcount
        // pkts_acked记录当前ACK应答触发的tcp_clean_rtx_queue函数调用一共处理了多少数据
		pkts_acked += acked_pcount;
        //通过ACK应答情况计算发送速率
		tcp_rate_skb_delivered(sk, skb, sack->rate);

		/* Initial outgoing SYN's get put onto the write_queue
		 * just like anything else we transmit.  It is not
		 * true data, and if we misinform our callers that
		 * this ACK acks real data, we will erroneously exit
		 * connection startup slow start one packet too
		 * quickly.  This is severely frowned upon behavior.
		 */
        // 区分是DATA应答还是SYN应答
		if (likely(!(scb->tcp_flags & TCPHDR_SYN))) {
			flag |= FLAG_DATA_ACKED;
		} else {
			flag |= FLAG_SYN_ACKED;
			tp->retrans_stamp = 0;
		}

        // 描述当前处理的大包是被整包应答还是部分应答
		if (!fully_acked)
			break;

		next = skb_rb_next(skb);
        // 下一个将要被重传的报文是当前处理的SKB，那么当前是顺序应答将retransmit_skb_hint置空
        // tp->retransmit_skb_hint描述的是下一次重传的其实位置
		if (unlikely(skb == tp->retransmit_skb_hint))
			tp->retransmit_skb_hint = NULL;
        //tp->lost_skb_hint描述的是下一次丢包标记的其实位置
		if (unlikely(skb == tp->lost_skb_hint))
			tp->lost_skb_hint = NULL;
		tcp_highest_sack_replace(sk, skb, next);
		tcp_rtx_queue_unlink_and_free(skb, sk);
	}

	if (!skb)
		tcp_chrono_stop(sk, TCP_CHRONO_BUSY);

	if (likely(between(tp->snd_up, prior_snd_una, tp->snd_una)))
		tp->snd_up = tp->snd_una;  /* 更新Urgent pointer */

	if (skb && (TCP_SKB_CB(skb)->sacked & TCPCB_SACKED_ACKED))
		flag |= FLAG_SACK_RENEGING; /* 虚假的SACK */

	if (likely(first_ackt) && !(flag & FLAG_RETRANS_DATA_ACKED)) {
		seq_rtt_us = tcp_stamp_us_delta(tp->tcp_mstamp, first_ackt);
		ca_rtt_us = tcp_stamp_us_delta(tp->tcp_mstamp, last_ackt);

		if (pkts_acked == 1 && last_in_flight < tp->mss_cache &&
		    last_in_flight && !prior_sacked && fully_acked &&
		    sack->rate->prior_delivered + 1 == tp->delivered &&
		    !(flag & (FLAG_CA_ALERT | FLAG_SYN_ACKED))) {
			/* Conservatively mark a delayed ACK. It's typically
			 * from a lone runt packet over the round trip to
			 * a receiver w/o out-of-order or CE events.
			 */
			flag |= FLAG_ACK_MAYBE_DELAYED;
		}
	}
	if (sack->first_sackt) {
		sack_rtt_us = tcp_stamp_us_delta(tp->tcp_mstamp, sack->first_sackt);
		ca_rtt_us = tcp_stamp_us_delta(tp->tcp_mstamp, sack->last_sackt);
	}
    /* 更新srtt、RTO等RTT相关变量*/
	rtt_update = tcp_ack_update_rtt(sk, flag, seq_rtt_us, sack_rtt_us,
					ca_rtt_us, sack->rate);

    /* 如果此ACK确认了新数据，使snd_una前进了*/
	if (flag & FLAG_ACKED) {
		flag |= FLAG_SET_XMIT_TIMER;  /* set TLP or RTO timer */
        /* 如果路径MTU的探测段被确认了*/
		if (unlikely(icsk->icsk_mtup.probe_size &&
			     !after(tp->mtu_probe.probe_seq_end, tp->snd_una))) {
			tcp_mtup_probe_success(sk);
		}

		if (tcp_is_reno(tp)) {
            /* Reno模拟SACK处理，更新tp->sacked_out。
             * 如果检测到乱序，更新tp->reordering。
             */
			tcp_remove_reno_sacks(sk, pkts_acked);

			/* If any of the cumulatively ACKed segments was
			 * retransmitted, non-SACK case cannot confirm that
			 * progress was due to original transmission due to
			 * lack of TCPCB_SACKED_ACKED bits even if some of
			 * the packets may have been never retransmitted.
			 */
			if (flag & FLAG_RETRANS_DATA_ACKED)
				flag &= ~FLAG_ORIG_SACK_ACKED;
		} else {
			int delta;

			/* Non-retransmitted hole got filled? That's reordering */
			// 如果之前没有SACK，prior_fackets为0，不会更新。
			if (before(reord, prior_fack))
				tcp_check_sack_reordering(sk, reord, 0);

			delta = prior_sacked - tp->sacked_out;
			tp->lost_cnt_hint -= min(tp->lost_cnt_hint, delta);
		}
	} else if (skb && rtt_update && sack_rtt_us >= 0 &&
		   sack_rtt_us > tcp_stamp_us_delta(tp->tcp_mstamp,
						    tcp_skb_timestamp_us(skb))) {
		/* Do not re-arm RTO if the sack RTT is measured from data sent
		 * after when the head was last (re)transmitted. Otherwise the
		 * timeout may continue to extend in loss recovery.
		 */
		flag |= FLAG_SET_XMIT_TIMER;  /* set TLP or RTO timer */
	}

    /* 如果定义了pkts_acked()钩子*/
	if (icsk->icsk_ca_ops->pkts_acked) {
		struct ack_sample sample = { .pkts_acked = pkts_acked,
					     .rtt_us = sack->rate->rtt_us,
					     .in_flight = last_in_flight };

		icsk->icsk_ca_ops->pkts_acked(sk, &sample);
	}

#if FASTRETRANS_DEBUG > 0
	WARN_ON((int)tp->sacked_out < 0);
	WARN_ON((int)tp->lost_out < 0);
	WARN_ON((int)tp->retrans_out < 0);
	if (!tp->packets_out && tcp_is_sack(tp)) {
		icsk = inet_csk(sk);
		if (tp->lost_out) {
			pr_debug("Leak l=%u %d\n",
				 tp->lost_out, icsk->icsk_ca_state);
			tp->lost_out = 0;
		}
		if (tp->sacked_out) {
			pr_debug("Leak s=%u %d\n",
				 tp->sacked_out, icsk->icsk_ca_state);
			tp->sacked_out = 0;
		}
		if (tp->retrans_out) {
			pr_debug("Leak r=%u %d\n",
				 tp->retrans_out, icsk->icsk_ca_state);
			tp->retrans_out = 0;
		}
	}
#endif
	return flag;
}

static void tcp_ack_probe(struct sock *sk)
{
	struct inet_connection_sock *icsk = inet_csk(sk);
	struct sk_buff *head = tcp_send_head(sk);
	const struct tcp_sock *tp = tcp_sk(sk);

	/* Was it a usable window open? */
	if (!head)
		return;
	if (!after(TCP_SKB_CB(head)->end_seq, tcp_wnd_end(tp))) {
		icsk->icsk_backoff = 0;
		inet_csk_clear_xmit_timer(sk, ICSK_TIME_PROBE0);
		/* Socket must be waked up by subsequent tcp_data_snd_check().
		 * This function is not for random using!
		 */
	} else {
		unsigned long when = tcp_probe0_when(sk, TCP_RTO_MAX);

		tcp_reset_xmit_timer(sk, ICSK_TIME_PROBE0,
				     when, TCP_RTO_MAX);
	}
}

static inline bool tcp_ack_is_dubious(const struct sock *sk, const int flag)
{
	return !(flag & FLAG_NOT_DUP) || (flag & FLAG_CA_ALERT) || // 是重复的ACK 或者 在进入拥塞状态的时候出现警告
		inet_csk(sk)->icsk_ca_state != TCP_CA_Open; // 或者拥塞状态不是“增大拥塞窗口”状态
}

/* Decide wheather to run the increase function of congestion control. */
static inline bool tcp_may_raise_cwnd(const struct sock *sk, const int flag)
{
	/* If reordering is high then always grow cwnd whenever data is
	 * delivered regardless of its ordering. Otherwise stay conservative
	 * and only grow cwnd on in-order delivery (RFC5681). A stretched ACK w/
	 * new SACK or ECE mark may first advance cwnd here and later reduce
	 * cwnd in tcp_fastretrans_alert() based on more states.
	 */
	if (tcp_sk(sk)->reordering > sock_net(sk)->ipv4.sysctl_tcp_reordering)
		return flag & FLAG_FORWARD_PROGRESS;

	return flag & FLAG_DATA_ACKED;
}

/* The "ultimate" congestion control function that aims to replace the rigid
 * cwnd increase and decrease control (tcp_cong_avoid,tcp_*cwnd_reduction).
 * It's called toward the end of processing an ACK with precise rate
 * information. All transmission or retransmission are delayed afterwards.
 */
static void tcp_cong_control(struct sock *sk, u32 ack, u32 acked_sacked,
			     int flag, const struct rate_sample *rs)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);

	//下面这个if是专门为bbr而做
	if (icsk->icsk_ca_ops->cong_control) {
        // 如果是bbr，则完全被bbr接管，不管现在处在什么状态！
        /* 目前而言，只有bbr使用了这个机制，但我相信，不久的将来，
         * 会有越来越多的拥塞控制算法使用这个统一的完全接管机制！
         * 就我个人而言，在几个月前就写过一个patch，接管了tcp_cwnd_reduction
         * 这个prr的降窗过程。如果当时有了这个框架，我就有福了！
         */
		icsk->icsk_ca_ops->cong_control(sk, rs);
		return;
	}

	if (tcp_in_cwnd_reduction(sk)) {
		/* Reduce cwnd if state mandates */
		tcp_cwnd_reduction(sk, acked_sacked, flag);
	} else if (tcp_may_raise_cwnd(sk, flag)) {
		/* Advance cwnd if state allows */
		tcp_cong_avoid(sk, ack, acked_sacked);
	}
	tcp_update_pacing_rate(sk);
}

/* Check that window update is acceptable.
 * The function assumes that snd_una<=ack<=snd_next.
 */
/*
 * 满足以下条件之一则更新：
 * (1) ACK确认了新的数据；
 * (2) 未满足(1)，ACK未确认数据，通过上面snd_una<=ack的条件，此时只能是snd_una=ack，
 * 即未确认新数据，是个重复ack，但是这个ack的序号比之前更新窗口的序号要新，则需要更新snd_wl1；
 * (3) 未满足(1)(2)，未确认数据，ack需要也未更新，但是窗口有所改变，
 * 则说明单单发送了一个窗口更新通知；
 *
 */
static inline bool tcp_may_update_window(const struct tcp_sock *tp,
					const u32 ack, const u32 ack_seq,
					const u32 nwin)
{
    /*
     * 更新条件
     * ack确认序号确认了数据，意味着窗口要收缩
     * ack确认序号未确认新数据，ack序号比上一个更新窗口ack序号要新
     * ack序号与上一个更新装ack序号一致，但是窗口比以前的窗口大
     * */
	return	after(ack, tp->snd_una) ||
		after(ack_seq, tp->snd_wl1) ||
		(ack_seq == tp->snd_wl1 && nwin > tp->snd_wnd); // 调整的新窗口大于原始发送窗口
}

/* If we update tp->snd_una, also update tp->bytes_acked */
static void tcp_snd_una_update(struct tcp_sock *tp, u32 ack)
{
	u32 delta = ack - tp->snd_una;

	sock_owned_by_me((struct sock *)tp);
	tp->bytes_acked += delta;
	tp->snd_una = ack;
}

/* If we update tp->rcv_nxt, also update tp->bytes_received */
static void tcp_rcv_nxt_update(struct tcp_sock *tp, u32 seq)
{
	u32 delta = seq - tp->rcv_nxt;

	sock_owned_by_me((struct sock *)tp);
	tp->bytes_received += delta;
	WRITE_ONCE(tp->rcv_nxt, seq);
}

/* Update our send window.
 *
 * Window update algorithm, described in RFC793/RFC1122 (used in linux-2.2
 * and in FreeBSD. NetBSD's one is even worse.) is wrong.
 */
static int tcp_ack_update_window(struct sock *sk, const struct sk_buff *skb, u32 ack,
				 u32 ack_seq)
{
	struct tcp_sock *tp = tcp_sk(sk); // 获得tcp_sock
	int flag = 0;
	u32 nwin = ntohs(tcp_hdr(skb)->window); // 获得skb发送方的可以接收的窗口值

    /* 根据扩大因子计算窗口大小 */
	if (likely(!tcp_hdr(skb)->syn))
		nwin <<= tp->rx_opt.snd_wscale;

    /* 需要更新窗口的话 */
	if (tcp_may_update_window(tp, ack, ack_seq, nwin)) {
        /* 窗口更新标记 */
		flag |= FLAG_WIN_UPDATE;
        /* 更新snd_wl1 */
		tcp_update_wl(tp, ack_seq);

        /* 发送窗口与通告窗口不等时 */
        // 如果发送窗口！= 缩放后的新窗口（注意skb发送方的接收窗口和本tp的发送窗口应该一致）
		if (tp->snd_wnd != nwin) {
            /* 更新发送窗口*/
			tp->snd_wnd = nwin;

			/* Note, it is the only place, where
			 * fast path is recovered for sending TCP.
			 */
            /* 判断是否开启快路标志 */
			tp->pred_flags = 0;
			tcp_fast_path_check(sk); // 检验是否能够开启“快速路径”看下面

            /* 有数据要发送 */
			if (!tcp_write_queue_empty(sk))
				tcp_slow_start_after_idle_check(sk);

            /* 窗口大于以前记录的最大窗口 */
			if (nwin > tp->max_window) {
                /* 更新最大窗口 */
				tp->max_window = nwin;
                /* 更新mss */
				tcp_sync_mss(sk, inet_csk(sk)->icsk_pmtu_cookie);
			}
		}
	}

    /* 更新未确认的数据位置，即窗口左边沿 */
	tcp_snd_una_update(tp, ack);

	return flag;
}

static bool __tcp_oow_rate_limited(struct net *net, int mib_idx,
				   u32 *last_oow_ack_time)
{
	if (*last_oow_ack_time) {
		s32 elapsed = (s32)(tcp_jiffies32 - *last_oow_ack_time);

		if (0 <= elapsed && elapsed < net->ipv4.sysctl_tcp_invalid_ratelimit) {
			NET_INC_STATS(net, mib_idx);
			return true;	/* rate-limited: don't send yet! */
		}
	}

	*last_oow_ack_time = tcp_jiffies32;

	return false;	/* not rate-limited: go ahead, send dupack now! */
}

/* Return true if we're currently rate-limiting out-of-window ACKs and
 * thus shouldn't send a dupack right now. We rate-limit dupacks in
 * response to out-of-window SYNs or ACKs to mitigate ACK loops or DoS
 * attacks that send repeated SYNs or ACKs for the same connection. To
 * do this, we do not send a duplicate SYNACK or ACK if the remote
 * endpoint is sending out-of-window SYNs or pure ACKs at a high rate.
 */
bool tcp_oow_rate_limited(struct net *net, const struct sk_buff *skb,
			  int mib_idx, u32 *last_oow_ack_time)
{
	/* Data packets without SYNs are not likely part of an ACK loop. */
	if ((TCP_SKB_CB(skb)->seq != TCP_SKB_CB(skb)->end_seq) &&
	    !tcp_hdr(skb)->syn)
		return false;

	return __tcp_oow_rate_limited(net, mib_idx, last_oow_ack_time);
}

/* RFC 5961 7 [ACK Throttling] */
static void tcp_send_challenge_ack(struct sock *sk, const struct sk_buff *skb)
{
	/* unprotected vars, we dont care of overwrites */
	static u32 challenge_timestamp;
	static unsigned int challenge_count;
	struct tcp_sock *tp = tcp_sk(sk);
	struct net *net = sock_net(sk);
	u32 count, now;

	/* First check our per-socket dupack rate limit. */
	if (__tcp_oow_rate_limited(net,
				   LINUX_MIB_TCPACKSKIPPEDCHALLENGE,
				   &tp->last_oow_ack_time))
		return;

	/* Then check host-wide RFC 5961 rate limit. */
	now = jiffies / HZ;
	if (now != challenge_timestamp) {
		u32 ack_limit = net->ipv4.sysctl_tcp_challenge_ack_limit;
		u32 half = (ack_limit + 1) >> 1;

		challenge_timestamp = now;
		WRITE_ONCE(challenge_count, half + prandom_u32_max(ack_limit));
	}
	count = READ_ONCE(challenge_count);
	if (count > 0) {
		WRITE_ONCE(challenge_count, count - 1);
		NET_INC_STATS(net, LINUX_MIB_TCPCHALLENGEACK);
		tcp_send_ack(sk);
	}
}

static void tcp_store_ts_recent(struct tcp_sock *tp)
{
	tp->rx_opt.ts_recent = tp->rx_opt.rcv_tsval;
	tp->rx_opt.ts_recent_stamp = ktime_get_seconds();
}

static void tcp_replace_ts_recent(struct tcp_sock *tp, u32 seq)
{
	if (tp->rx_opt.saw_tstamp && !after(seq, tp->rcv_wup)) {
		/* PAWS bug workaround wrt. ACK frames, the PAWS discard
		 * extra check below makes sure this can only happen
		 * for pure ACK frames.  -DaveM
		 *
		 * Not only, also it occurs for expired timestamps.
		 */

		if (tcp_paws_check(&tp->rx_opt, 0))
			tcp_store_ts_recent(tp);
	}
}

/* This routine deals with acks during a TLP episode.
 * We mark the end of a TLP episode on receiving TLP dupack or when
 * ack is after tlp_high_seq.
 * Ref: loss detection algorithm in draft-dukkipati-tcpm-tcp-loss-probe.
 * 何时结束一个episode
 */
static void tcp_process_tlp_ack(struct sock *sk, u32 ack, int flag)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (before(ack, tp->tlp_high_seq))
		return;

	// FLAG_DSACKING_ACK ->SACK blocks contained D-SACK info
	if (flag & FLAG_DSACKING_ACK) {
	    // 如果此ACK报文中包含重复SACK（DSACK）块，说明对端收到了原始和TLP探测两份报文，没有丢失情况发生，清空tlp_high_seq
		/* This DSACK means original and TLP probe arrived; no loss */
		tp->tlp_high_seq = 0;
	} else if (after(ack, tp->tlp_high_seq)) {
		/* ACK advances: there was a loss, so reduce cwnd. Reset
		 * tlp_high_seq in tcp_init_cwnd_reduction()
		 */
		// 如果ACK确认序号在tlp_high_seq序号之后，表明未接收到对TLP探测报文的确认，
		// 报文已经丢失，将在函数tcp_init_cwnd_reduction中清零tlp_high_seq
		/* 最关键的就是降cwnd: ssthresh = 0.7*cwnd; cwnd=ssthresh */
		tcp_init_cwnd_reduction(sk);
		tcp_set_ca_state(sk, TCP_CA_CWR);
		tcp_end_cwnd_reduction(sk);
		tcp_try_keep_open(sk);
		NET_INC_STATS(sock_net(sk),
				LINUX_MIB_TCPLOSSPROBERECOVERY);
	} else if (!(flag & (FLAG_SND_UNA_ADVANCED |
			     FLAG_NOT_DUP | FLAG_DATA_SACKED))) {
	    // 如果ACK确认了TLP探测报文，并且此ACK报文并没有移动SND.UNA值，也不携带数据，并非窗口更新，
	    // 也没有包含SACK块，表明其为一个单纯的重复ACK报文，即对端已经接收到原始的报文和TLP探测报文，
	    // 清零tlp_high_seq，结束TLP
		/* Pure dupack: original and TLP probe arrived; no loss */
		tp->tlp_high_seq = 0;
	}
}

static inline void tcp_in_ack_event(struct sock *sk, u32 flags)
{
	const struct inet_connection_sock *icsk = inet_csk(sk);

	if (icsk->icsk_ca_ops->in_ack_event)
		icsk->icsk_ca_ops->in_ack_event(sk, flags);
}

/* Congestion control has updated the cwnd already. So if we're in
 * loss recovery then now we do any new sends (for FRTO) or
 * retransmits (for CA_Loss or CA_recovery) that make sense.
 */
static void tcp_xmit_recovery(struct sock *sk, int rexmit)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (rexmit == REXMIT_NONE || sk->sk_state == TCP_SYN_SENT)
		return;

	if (unlikely(rexmit == REXMIT_NEW)) {
		__tcp_push_pending_frames(sk, tcp_current_mss(sk),
					  TCP_NAGLE_OFF);  // //F-FTO发送新数据
		if (after(tp->snd_nxt, tp->high_seq)) // 有新数据发送则返回，不重传
			return;
		tp->frto = 0;
	}
	tcp_xmit_retransmit_queue(sk); // 重传重传队列中那些标记为LOST的段，同时重置 RTO 定时器
}

/* Returns the number of packets newly acked or sacked by the current ACK */
static u32 tcp_newly_delivered(struct sock *sk, u32 prior_delivered, int flag)
{
	const struct net *net = sock_net(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	u32 delivered;

	// 使用当前套接口中更新的delivered计数减去之前的旧值prior_delivered，得到本次ACK处理，确认的报文数量
	delivered = tp->delivered - prior_delivered;
	NET_ADD_STATS(net, LINUX_MIB_TCPDELIVERED, delivered);
	if (flag & FLAG_ECE) {
		tp->delivered_ce += delivered;
		NET_ADD_STATS(net, LINUX_MIB_TCPDELIVEREDCE, delivered);
	}
	return delivered;
}

/* This routine deals with incoming acks, but not outgoing ones. */
/*
 * 1 更新重传队列。
 * 2 更新发送窗口。
 * 3 从sack的信息或者重复ack来决定是否进入拥塞模式
 */
static int tcp_ack(struct sock *sk, const struct sk_buff *skb, int flag)
{
	struct inet_connection_sock *icsk = inet_csk(sk); // 获得连接sock
	struct tcp_sock *tp = tcp_sk(sk); // 获得tcp_sock
	struct tcp_sacktag_state sack_state;
	struct rate_sample rs = { .prior_delivered = 0 };
	u32 prior_snd_una = tp->snd_una; // 获得未发送确认的序号
	bool is_sack_reneg = tp->is_sack_reneg; // 是否发生了乱序
	u32 ack_seq = TCP_SKB_CB(skb)->seq; // 获得数据序号
	u32 ack = TCP_SKB_CB(skb)->ack_seq; // 获得ack序号(用于确认的序号)
	int num_dupack = 0;
	int prior_packets = tp->packets_out; // 获得发出去没有收到确认的包数量
	u32 delivered = tp->delivered;
	u32 lost = tp->lost;
	int rexmit = REXMIT_NONE; /* Flag to (re)transmit to recover losses */
	u32 prior_fack;

	sack_state.first_sackt = 0;
	sack_state.rate = &rs;

	/* We very likely will need to access rtx queue. */
	prefetch(sk->tcp_rtx_queue.rb_node);

	/* If the ack is older than previous acks
	 * then we can probably ignore it.
	 */
    // 如果ack确认比我期望的确认序号小，那么可能是以前老的ack
	if (before(ack, prior_snd_una)) {
		/* RFC 5961 5.2 [Blind Data Injection Attack].[Mitigation] */
		if (before(ack, prior_snd_una - tp->max_window)) {
		    // 如果接收到的ack比 之前第一个未ack的ack值-接收端历史最大的窗口值
		    // 认为是发生了虚假数据注入攻击
			if (!(flag & FLAG_NO_CHALLENGE_ACK))
				tcp_send_challenge_ack(sk, skb);
			return -1;
		}
		goto old_ack;
	}

	/* If the ack includes data we haven't sent yet, discard
	 * this segment (RFC793 Section 3.9).
	 */
    // 如果确认序号比我还下一个准备发送的序号还要大，即确认了我们尚未发送的数据，那么显然不合理
	if (after(ack, tp->snd_nxt))
		return -1;

    // 如果ack确认比我期望的第一个ack要大，但是经过上面我们还知道没有超过我没有发送的数据序号范围
	if (after(ack, prior_snd_una)) {
        // 那么设置标识
		flag |= FLAG_SND_UNA_ADVANCED;
		icsk->icsk_retransmits = 0;

#if IS_ENABLED(CONFIG_TLS_DEVICE)
		if (static_branch_unlikely(&clean_acked_data_enabled.key))
			if (icsk->icsk_clean_acked)
				icsk->icsk_clean_acked(sk, ack);
#endif
	}

	prior_fack = tcp_is_sack(tp) ? tcp_highest_sack_seq(tp) : tp->snd_una;
    // 计算还在传输的数据段的字节数，下面会说手这个函数
	rs.prior_in_flight = tcp_packets_in_flight(tp);

	/* ts_recent update must be made after we are sure that the packet
	 * is in window.
	 */
	if (flag & FLAG_UPDATE_TS_RECENT)
		tcp_replace_ts_recent(tp, TCP_SKB_CB(skb)->seq);

    /* 快速路径&& ack比我期望的第一个ack大但是未超出序号范围 */
	if ((flag & (FLAG_SLOWPATH | FLAG_SND_UNA_ADVANCED)) ==
	    FLAG_SND_UNA_ADVANCED) {
        // 如果不是“慢路径” && ack确认比其需要的第一个大(正确的确认序号)
		/* Window is constant, pure forward advance.
		 * No more checks are required.
		 * Note, we use the fact that SND.UNA>=SND.WL2.
		 */
        // 需要更新sock中的snd_wl1字段
		tcp_update_wl(tp, ack_seq);
        /* 更新未确认的数据位置，即窗口左边沿 */
		tcp_snd_una_update(tp, ack);
		flag |= FLAG_WIN_UPDATE; // 窗口更新标识

        //如果拥塞控制算法有in_ack_event方法，便调用
		tcp_in_ack_event(sk, CA_ACK_WIN_UPDATE);

		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPHPACKS);
	} else {
		u32 ack_ev_flags = CA_ACK_SLOWPATH;

		if (ack_seq != TCP_SKB_CB(skb)->end_seq)
            // 如果不相等，那么说明还是带有数据一起的，不仅仅是一个ACK的包
			flag |= FLAG_DATA;
		else
			NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPPUREACKS);// 否则仅仅是ACK的包

        // 更新发送窗口
		flag |= tcp_ack_update_window(sk, skb, ack, ack_seq);

		if (TCP_SKB_CB(skb)->sacked)
            // 然后判断是否有 sack 段，有的话，我们进入 sack 段的处理。
			flag |= tcp_sacktag_write_queue(sk, skb, prior_snd_una,
							&sack_state);

		if (tcp_ecn_rcv_ecn_echo(tp, tcp_hdr(skb))) {
            // 判断是否有ecn标记，如果有的话，设置ecn标记。
			flag |= FLAG_ECE;
			ack_ev_flags |= CA_ACK_ECE;
		}

		if (flag & FLAG_WIN_UPDATE)
			ack_ev_flags |= CA_ACK_WIN_UPDATE;

        //如果拥塞控制算法有 in_ack_event 方法，便调用
		tcp_in_ack_event(sk, ack_ev_flags);
	}

	/* This is a deviation from RFC3168 since it states that:
	 * "When the TCP data sender is ready to set the CWR bit after reducing
	 * the congestion window, it SHOULD set the CWR bit only on the first
	 * new data packet that it transmits."
	 * We accept CWR on pure ACKs to be more robust
	 * with widely-deployed TCP implementations that do this.
	 */
    /* 如果收到对方发来的CWR，则本地TCP发送时不在设置ECE*/
	tcp_ecn_accept_cwr(sk, skb);

	/* We passed data and got it acked, remove any soft error
	 * log. Something worked...
	 */
	sk->sk_err_soft = 0;
	icsk->icsk_probes_out = 0;
	tp->rcv_tstamp = tcp_jiffies32;
	// packets_out为0，但是sk_send_head不为0，表示本段数据发送不出去
	if (!prior_packets)
        // 如果为0，则可能是0窗口探测包
		goto no_queue;

	/* See if we can take anything off of the retransmit queue. */
    // 清理重传队列中的已经确认的数据段
	flag |= tcp_clean_rtx_queue(sk, prior_fack, prior_snd_una, &sack_state);

	tcp_rack_update_reo_wnd(sk, &rs);

	if (tp->tlp_high_seq)
	    // 如果tlp_high_seq有值，表明发送了TLP探测报文，由函数tcp_process_tlp_ack处理ACK
		tcp_process_tlp_ack(sk, ack, flag); /* 判断是否需要结束TLP状态 */
	/* If needed, reset TLP/RTO timer; RACK may later override this. */
	if (flag & FLAG_SET_XMIT_TIMER)
	    // 标志标量flag如果设置了FLAG_SET_XMIT_TIMER，表明此ACK报文确认了新的数据，需要重新调整TLP/RTO定时器
		tcp_set_xmit_timer(sk); //安装PTO超时计时器

    if (tcp_ack_is_dubious(sk, flag)) {
        // 判断ack是否可疑，其实本质就是判断可不可以增大拥塞窗口
        // 这个ACK是可疑的，其实意思就是，不是一个正常的ACK，不能随便增大拥塞窗口

		if (!(flag & (FLAG_SND_UNA_ADVANCED | FLAG_NOT_DUP))) {
			num_dupack = 1;
			/* Consider if pure acks were aggregated in tcp_add_backlog() */
			if (!(flag & FLAG_DATA))
				num_dupack = max_t(u16, 1, skb_shinfo(skb)->gso_segs);
		}
        // 这里进入拥塞状态的处理，非常重要的函数(对于拥塞处理来说)
		tcp_fastretrans_alert(sk, prior_snd_una, num_dupack, &flag,
				      &rexmit);
	}

	if ((flag & FLAG_FORWARD_PROGRESS) || !(flag & FLAG_NOT_DUP))
		sk_dst_confirm(sk);

	delivered = tcp_newly_delivered(sk, delivered, flag);     // 确认的报文数量
	lost = tp->lost - lost;			/* freshly marked lost */ // 丢失报文数量
	rs.is_ack_delayed = !!(flag & FLAG_ACK_MAYBE_DELAYED);
	// 速率样本生成
	tcp_rate_gen(sk, delivered, lost, is_sack_reneg, sack_state.rate);
	// 进入拥塞控制算法操作
	tcp_cong_control(sk, ack, delivered, flag, sack_state.rate);
	tcp_xmit_recovery(sk, rexmit);
	return 1;

no_queue:
	/* If data was DSACKed, see if we can undo a cwnd reduction. */
	if (flag & FLAG_DSACKING_ACK) {
		tcp_fastretrans_alert(sk, prior_snd_una, num_dupack, &flag,
				      &rexmit);
		tcp_newly_delivered(sk, delivered, flag);
	}
	/* If this ack opens up a zero window, clear backoff.  It was
	 * being used to time the probes, and is probably far higher than
	 * it needs to be for normal retransmission.
	 */
    // 处理定时器函数
	tcp_ack_probe(sk);

	if (tp->tlp_high_seq)
        // tlp_high_seq有值，表明发送了TLP探测报文，由函数tcp_process_tlp_ack处理ACK
		tcp_process_tlp_ack(sk, ack, flag);
	return 1;

old_ack:
	/* If data was SACKed, tag it and see if we should send more data.
	 * If data was DSACKed, see if we can undo a cwnd reduction.
	 */
	if (TCP_SKB_CB(skb)->sacked) {
		flag |= tcp_sacktag_write_queue(sk, skb, prior_snd_una,
						&sack_state);
		tcp_fastretrans_alert(sk, prior_snd_una, num_dupack, &flag,
				      &rexmit);
		tcp_newly_delivered(sk, delivered, flag);
		tcp_xmit_recovery(sk, rexmit);
	}

	return 0;
}

static void tcp_parse_fastopen_option(int len, const unsigned char *cookie,
				      bool syn, struct tcp_fastopen_cookie *foc,
				      bool exp_opt)
{
	/* Valid only in SYN or SYN-ACK with an even length.  */
	if (!foc || !syn || len < 0 || (len & 1))
		return;

	if (len >= TCP_FASTOPEN_COOKIE_MIN &&
	    len <= TCP_FASTOPEN_COOKIE_MAX)
		memcpy(foc->val, cookie, len);
	else if (len != 0)
		len = -1;
	foc->len = len;
	foc->exp = exp_opt;
}

static void smc_parse_options(const struct tcphdr *th,
			      struct tcp_options_received *opt_rx,
			      const unsigned char *ptr,
			      int opsize)
{
#if IS_ENABLED(CONFIG_SMC)
	if (static_branch_unlikely(&tcp_have_smc)) {
		if (th->syn && !(opsize & 1) &&
		    opsize >= TCPOLEN_EXP_SMC_BASE &&
		    get_unaligned_be32(ptr) == TCPOPT_SMC_MAGIC)
			opt_rx->smc_ok = 1;
	}
#endif
}

/* Try to parse the MSS option from the TCP header. Return 0 on failure, clamped
 * value on success.
 */
static u16 tcp_parse_mss_option(const struct tcphdr *th, u16 user_mss)
{
	const unsigned char *ptr = (const unsigned char *)(th + 1);
	int length = (th->doff * 4) - sizeof(struct tcphdr);
	u16 mss = 0;

	while (length > 0) {
		int opcode = *ptr++;
		int opsize;

		switch (opcode) {
		case TCPOPT_EOL:
			return mss;
		case TCPOPT_NOP:	/* Ref: RFC 793 section 3.1 */
			length--;
			continue;
		default:
			if (length < 2)
				return mss;
			opsize = *ptr++;
			if (opsize < 2) /* "silly options" */
				return mss;
			if (opsize > length)
				return mss;	/* fail on partial options */
			if (opcode == TCPOPT_MSS && opsize == TCPOLEN_MSS) {
				u16 in_mss = get_unaligned_be16(ptr);

				if (in_mss) {
					if (user_mss && user_mss < in_mss)
						in_mss = user_mss;
					mss = in_mss;
				}
			}
			ptr += opsize - 2;
			length -= opsize;
		}
	}
	return mss;
}

/* Look for tcp options. Normally only called on SYN and SYNACK packets.
 * But, this can also be called on packets in the established flow when
 * the fast version below fails.
 */
void tcp_parse_options(const struct net *net,
		       const struct sk_buff *skb,
		       struct tcp_options_received *opt_rx, int estab,
		       struct tcp_fastopen_cookie *foc)
{
	const unsigned char *ptr;
	const struct tcphdr *th = tcp_hdr(skb);
	int length = (th->doff * 4) - sizeof(struct tcphdr);

	ptr = (const unsigned char *)(th + 1);
	opt_rx->saw_tstamp = 0;

	while (length > 0) {
		int opcode = *ptr++;
		int opsize;

		switch (opcode) {
		case TCPOPT_EOL:
			return;
		case TCPOPT_NOP:	/* Ref: RFC 793 section 3.1 */
			length--;
			continue;
		default:
			if (length < 2)
				return;
			opsize = *ptr++;
			if (opsize < 2) /* "silly options" */
				return;
			if (opsize > length)
				return;	/* don't parse partial options */
			switch (opcode) {
			case TCPOPT_MSS:
				if (opsize == TCPOLEN_MSS && th->syn && !estab) {
					u16 in_mss = get_unaligned_be16(ptr);
					if (in_mss) {
						if (opt_rx->user_mss &&
						    opt_rx->user_mss < in_mss)
							in_mss = opt_rx->user_mss;
						opt_rx->mss_clamp = in_mss;
					}
				}
				break;
			case TCPOPT_WINDOW:
				if (opsize == TCPOLEN_WINDOW && th->syn &&
				    !estab && net->ipv4.sysctl_tcp_window_scaling) {
					__u8 snd_wscale = *(__u8 *)ptr;
					opt_rx->wscale_ok = 1;
					if (snd_wscale > TCP_MAX_WSCALE) {
						net_info_ratelimited("%s: Illegal window scaling value %d > %u received\n",
								     __func__,
								     snd_wscale,
								     TCP_MAX_WSCALE);
						snd_wscale = TCP_MAX_WSCALE;
					}
					opt_rx->snd_wscale = snd_wscale;
				}
				break;
			case TCPOPT_TIMESTAMP:
				if ((opsize == TCPOLEN_TIMESTAMP) &&
				    ((estab && opt_rx->tstamp_ok) ||
				     (!estab && net->ipv4.sysctl_tcp_timestamps))) {
					opt_rx->saw_tstamp = 1;
					opt_rx->rcv_tsval = get_unaligned_be32(ptr);
					opt_rx->rcv_tsecr = get_unaligned_be32(ptr + 4);
				}
				break;
			case TCPOPT_SACK_PERM:
				if (opsize == TCPOLEN_SACK_PERM && th->syn &&
				    !estab && net->ipv4.sysctl_tcp_sack) {
					opt_rx->sack_ok = TCP_SACK_SEEN;
					tcp_sack_reset(opt_rx);
				}
				break;

			case TCPOPT_SACK:
				if ((opsize >= (TCPOLEN_SACK_BASE + TCPOLEN_SACK_PERBLOCK)) &&
				   !((opsize - TCPOLEN_SACK_BASE) % TCPOLEN_SACK_PERBLOCK) &&
				   opt_rx->sack_ok) {
					TCP_SKB_CB(skb)->sacked = (ptr - 2) - (unsigned char *)th;
				}
				break;
#ifdef CONFIG_TCP_MD5SIG
			case TCPOPT_MD5SIG:
				/*
				 * The MD5 Hash has already been
				 * checked (see tcp_v{4,6}_do_rcv()).
				 */
				break;
#endif
			case TCPOPT_FASTOPEN:
				tcp_parse_fastopen_option(
					opsize - TCPOLEN_FASTOPEN_BASE,
					ptr, th->syn, foc, false);
				break;

			case TCPOPT_EXP:
				/* Fast Open option shares code 254 using a
				 * 16 bits magic number.
				 */
				if (opsize >= TCPOLEN_EXP_FASTOPEN_BASE &&
				    get_unaligned_be16(ptr) ==
				    TCPOPT_FASTOPEN_MAGIC)
					tcp_parse_fastopen_option(opsize -
						TCPOLEN_EXP_FASTOPEN_BASE,
						ptr + 2, th->syn, foc, true);
				else
					smc_parse_options(th, opt_rx, ptr,
							  opsize);
				break;

			}
			ptr += opsize-2;
			length -= opsize;
		}
	}
}
EXPORT_SYMBOL(tcp_parse_options);

static bool tcp_parse_aligned_timestamp(struct tcp_sock *tp, const struct tcphdr *th)
{
	const __be32 *ptr = (const __be32 *)(th + 1);

	if (*ptr == htonl((TCPOPT_NOP << 24) | (TCPOPT_NOP << 16)
			  | (TCPOPT_TIMESTAMP << 8) | TCPOLEN_TIMESTAMP)) {
		tp->rx_opt.saw_tstamp = 1;
		++ptr;
		tp->rx_opt.rcv_tsval = ntohl(*ptr);
		++ptr;
		if (*ptr)
			tp->rx_opt.rcv_tsecr = ntohl(*ptr) - tp->tsoffset;
		else
			tp->rx_opt.rcv_tsecr = 0;
		return true;
	}
	return false;
}

/* Fast parse options. This hopes to only see timestamps.
 * If it is wrong it falls back on tcp_parse_options().
 */
static bool tcp_fast_parse_options(const struct net *net,
				   const struct sk_buff *skb,
				   const struct tcphdr *th, struct tcp_sock *tp)
{
	/* In the spirit of fast parsing, compare doff directly to constant
	 * values.  Because equality is used, short doff can be ignored here.
	 */
	if (th->doff == (sizeof(*th) / 4)) {
		tp->rx_opt.saw_tstamp = 0;
		return false;
	} else if (tp->rx_opt.tstamp_ok &&
		   th->doff == ((sizeof(*th) + TCPOLEN_TSTAMP_ALIGNED) / 4)) {
		if (tcp_parse_aligned_timestamp(tp, th))
			return true;
	}

	tcp_parse_options(net, skb, &tp->rx_opt, 1, NULL);
	if (tp->rx_opt.saw_tstamp && tp->rx_opt.rcv_tsecr)
		tp->rx_opt.rcv_tsecr -= tp->tsoffset;

	return true;
}

#ifdef CONFIG_TCP_MD5SIG
/*
 * Parse MD5 Signature option
 */
const u8 *tcp_parse_md5sig_option(const struct tcphdr *th)
{
	int length = (th->doff << 2) - sizeof(*th);
	const u8 *ptr = (const u8 *)(th + 1);

	/* If not enough data remaining, we can short cut */
	while (length >= TCPOLEN_MD5SIG) {
		int opcode = *ptr++;
		int opsize;

		switch (opcode) {
		case TCPOPT_EOL:
			return NULL;
		case TCPOPT_NOP:
			length--;
			continue;
		default:
			opsize = *ptr++;
			if (opsize < 2 || opsize > length)
				return NULL;
			if (opcode == TCPOPT_MD5SIG)
				return opsize == TCPOLEN_MD5SIG ? ptr : NULL;
		}
		ptr += opsize - 2;
		length -= opsize;
	}
	return NULL;
}
EXPORT_SYMBOL(tcp_parse_md5sig_option);
#endif

/* Sorry, PAWS as specified is broken wrt. pure-ACKs -DaveM
 *
 * It is not fatal. If this ACK does _not_ change critical state (seqs, window)
 * it can pass through stack. So, the following predicate verifies that
 * this segment is not used for anything but congestion avoidance or
 * fast retransmit. Moreover, we even are able to eliminate most of such
 * second order effects, if we apply some small "replay" window (~RTO)
 * to timestamp space.
 *
 * All these measures still do not guarantee that we reject wrapped ACKs
 * on networks with high bandwidth, when sequence space is recycled fastly,
 * but it guarantees that such events will be very rare and do not affect
 * connection seriously. This doesn't look nice, but alas, PAWS is really
 * buggy extension.
 *
 * [ Later note. Even worse! It is buggy for segments _with_ data. RFC
 * states that events when retransmit arrives after original data are rare.
 * It is a blatant lie. VJ forgot about fast retransmit! 8)8) It is
 * the biggest problem on large power networks even with minor reordering.
 * OK, let's give it small replay window. If peer clock is even 1hz, it is safe
 * up to bandwidth of 18Gigabit/sec. 8) ]
 */

/*
 * local方通过tcp_disordered_ack函数对一个刚收到的数据分段进行判断，下面我们对该函数的判断逻辑进行下总结：
 * 大前提：该收到分段的TS值表明有回绕现象发生
 * a）若该分段不是一个纯ACK，则丢弃。因为显然这个分段所携带的数据是一个老数据了，不是local方目前希望接收的（参见PAWS的处理依据一节）
 * b）若该分段不是local所希望接收的，则丢弃。这个原因很显然
 * c）若该分段是一个纯ACK，但该ACK并不是一个重复ACK（由local方后续数据正确到达所引发的），则丢弃。因为显然该ACK是一个老的ACK，并不是由于为了加快local方重发而在每收到一个丢失分段后的分段而发出的ACK。
 * d）若该分段是一个ACK，且为重复ACK，并且该ACK的TS值超过了local方那个丢失分段后的重发rto，则丢弃。因为显然此时local方已经重发了那个导致此重复ACK产生的分段，因此再收到此重复ACK就可以直接丢弃。
 * e）若该分段是一个ACK，且为重复ACK，但是没有超过一个rto的时间，则不能丢弃，因为这正代表peer方收到了local方发出的丢失分段后的分段，local方要对此ACK进行处理（例如立刻重传）
 *
 * 这里有一个重要概念需要理解，即在出现TS问题后，纯ACK和带ACK的数据分段二者是显著不同的，对于后者，可以立刻丢弃掉，因为从一个窗口的某个seq到下一个窗口的同一个seq过程中，一定有窗口变化曾经发生过，从而TS记录值ts_recent也一定更新过，此时一定可以通过PAWS进行丢弃处理。但是对于前者，一个纯ACK，就不能简单丢弃了，因为有这样一个现象是合理的，即假定local方的接收缓存很大，并且peer方在发送时很快就回绕了，于是在local方的某个分段丢失后，peer方需要在每收到的后续分段时发送重复ACK，而此时该重发ACK的ack_seq就是这个丢失分段的序号，而该重发ACK的seq已经是回绕后的重复序号了，尽管此时到底是回绕后的那个重复ACK还是之前的那个同样序号seq的重复ACK，对于local方来都需要处理（立刻启动重发动作），而不能简单丢弃掉。
 */
static int tcp_disordered_ack(const struct sock *sk, const struct sk_buff *skb)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	const struct tcphdr *th = tcp_hdr(skb);
	u32 seq = TCP_SKB_CB(skb)->seq;
	u32 ack = TCP_SKB_CB(skb)->ack_seq;

	return (/* 1. Pure ACK with correct sequence number. */
		(th->ack && seq == TCP_SKB_CB(skb)->end_seq && seq == tp->rcv_nxt) &&

		/* 2. ... and duplicate ACK. */
		ack == tp->snd_una &&

		/* 3. ... and does not update window. */
		!tcp_may_update_window(tp, ack, seq, ntohs(th->window) << tp->rx_opt.snd_wscale) &&

		/* 4. ... and sits in replay window. */
		(s32)(tp->rx_opt.ts_recent - tp->rx_opt.rcv_tsval) <= (inet_csk(sk)->icsk_rto * 1024) / HZ);
}

/*
 * 1 The difference between the timestamp value obtained in the current segmentand last seen timestamp on the incoming TCP segment should be more than TCP_PAWS_WINDOW (= 1),
 * which means that if the segment that was transmitted 1 clock tick before the segment that reached here earlier TCP seq should be acceptable.
 * It may be because of reordering of the segments that the latter reached earlier.
 * 2 the 24 days have not elapsed since last time timestamp was stored,
 * 3 tcp_disordered_ack返回0.
 */
static inline bool tcp_paws_discard(const struct sock *sk,
				   const struct sk_buff *skb)
{
	const struct tcp_sock *tp = tcp_sk(sk);

	return !tcp_paws_check(&tp->rx_opt, TCP_PAWS_WINDOW) &&
	       !tcp_disordered_ack(sk, skb);
}

/* Check segment sequence number for validity.
 *
 * Segment controls are considered valid, if the segment
 * fits to the window after truncation to the window. Acceptability
 * of data (and SYN, FIN, of course) is checked separately.
 * See tcp_data_queue(), for example.
 *
 * Also, controls (RST is main one) are accepted using RCV.WUP instead
 * of RCV.NXT. Peer still did not advance his SND.UNA when we
 * delayed ACK, so that hisSND.UNA<=ourRCV.WUP.
 * (borrowed from freebsd)
 */
// 由rcv_wup的更新时机（发送ACK时的tcp_select_window）可知位于序号rcv_wup前面的数据都已确认，
// 所以待检查数据包的结束序号至少要大于该值；
// 同时开始序号要落在接收窗口内。
static inline bool tcp_sequence(const struct tcp_sock *tp, u32 seq, u32 end_seq)
{
	return	!before(end_seq, tp->rcv_wup) &&
		!after(seq, tp->rcv_nxt + tcp_receive_window(tp));
}

/* When we get a reset we do this. */
void tcp_reset(struct sock *sk)
{
	trace_tcp_receive_reset(sk);

	/* We want the right error as BSD sees it (and indeed as we do). */
	switch (sk->sk_state) {
	case TCP_SYN_SENT:
		sk->sk_err = ECONNREFUSED;
		break;
	case TCP_CLOSE_WAIT:
		sk->sk_err = EPIPE;
		break;
	case TCP_CLOSE:
		return;
	default:
		sk->sk_err = ECONNRESET;
	}
	/* This barrier is coupled with smp_rmb() in tcp_poll() */
	smp_wmb();

	tcp_write_queue_purge(sk);
	tcp_done(sk);

	if (!sock_flag(sk, SOCK_DEAD))
		sk->sk_error_report(sk);
}

/*
 * 	Process the FIN bit. This now behaves as it is supposed to work
 *	and the FIN takes effect when it is validly part of sequence
 *	space. Not before when we get holes.
 *
 *	If we are ESTABLISHED, a received fin moves us to CLOSE-WAIT
 *	(and thence onto LAST-ACK and finally, CLOSE, we never enter
 *	TIME-WAIT)
 *
 *	If we are in FINWAIT-1, a received FIN indicates simultaneous
 *	close and we go into CLOSING (and later onto TIME-WAIT)
 *
 *	If we are in FINWAIT-2, a received FIN moves us to TIME-WAIT.
 */
void tcp_fin(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	inet_csk_schedule_ack(sk);

	sk->sk_shutdown |= RCV_SHUTDOWN;
	sock_set_flag(sk, SOCK_DONE);

	switch (sk->sk_state) {
	case TCP_SYN_RECV:
	case TCP_ESTABLISHED:
		/* Move to CLOSE_WAIT */
		tcp_set_state(sk, TCP_CLOSE_WAIT);
		inet_csk_enter_pingpong_mode(sk);
		break;

	case TCP_CLOSE_WAIT:
	case TCP_CLOSING:
		/* Received a retransmission of the FIN, do
		 * nothing.
		 */
		break;
	case TCP_LAST_ACK:
		/* RFC793: Remain in the LAST-ACK state. */
		break;

	case TCP_FIN_WAIT1:
		/* This case occurs when a simultaneous close
		 * happens, we must ack the received FIN and
		 * enter the CLOSING state.
		 */
		tcp_send_ack(sk);
		tcp_set_state(sk, TCP_CLOSING);
		break;
	case TCP_FIN_WAIT2:
		/* Received a FIN -- send ACK and enter TIME_WAIT. */
		tcp_send_ack(sk);
		tcp_time_wait(sk, TCP_TIME_WAIT, 0);
		break;
	default:
		/* Only TCP_LISTEN and TCP_CLOSE are left, in these
		 * cases we should never reach this piece of code.
		 */
		pr_err("%s: Impossible, sk->sk_state=%d\n",
		       __func__, sk->sk_state);
		break;
	}

	/* It _is_ possible, that we have something out-of-order _after_ FIN.
	 * Probably, we should reset in this case. For now drop them.
	 */
	skb_rbtree_purge(&tp->out_of_order_queue);
	if (tcp_is_sack(tp))
		tcp_sack_reset(&tp->rx_opt);
	sk_mem_reclaim(sk);

	if (!sock_flag(sk, SOCK_DEAD)) {
		sk->sk_state_change(sk);

		/* Do not send POLL_HUP for half duplex close. */
		if (sk->sk_shutdown == SHUTDOWN_MASK ||
		    sk->sk_state == TCP_CLOSE)
			sk_wake_async(sk, SOCK_WAKE_WAITD, POLL_HUP);
		else
			sk_wake_async(sk, SOCK_WAKE_WAITD, POLL_IN);
	}
}

static inline bool tcp_sack_extend(struct tcp_sack_block *sp, u32 seq,
				  u32 end_seq)
{
	if (!after(seq, sp->end_seq) && !after(sp->start_seq, end_seq)) {
		if (before(seq, sp->start_seq))
			sp->start_seq = seq;
		if (after(end_seq, sp->end_seq))
			sp->end_seq = end_seq;
		return true;
	}
	return false;
}

static void tcp_dsack_set(struct sock *sk, u32 seq, u32 end_seq)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (tcp_is_sack(tp) && sock_net(sk)->ipv4.sysctl_tcp_dsack) {
		int mib_idx;

		if (before(seq, tp->rcv_nxt))
			mib_idx = LINUX_MIB_TCPDSACKOLDSENT;
		else
			mib_idx = LINUX_MIB_TCPDSACKOFOSENT;

		NET_INC_STATS(sock_net(sk), mib_idx);

		tp->rx_opt.dsack = 1;
		tp->duplicate_sack[0].start_seq = seq;
		tp->duplicate_sack[0].end_seq = end_seq;
	}
}

static void tcp_dsack_extend(struct sock *sk, u32 seq, u32 end_seq)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (!tp->rx_opt.dsack)
		tcp_dsack_set(sk, seq, end_seq);
	else
		tcp_sack_extend(tp->duplicate_sack, seq, end_seq);
}

static void tcp_rcv_spurious_retrans(struct sock *sk, const struct sk_buff *skb)
{
	/* When the ACK path fails or drops most ACKs, the sender would
	 * timeout and spuriously retransmit the same segment repeatedly.
	 * The receiver remembers and reflects via DSACKs. Leverage the
	 * DSACK state and change the txhash to re-route speculatively.
	 */
	if (TCP_SKB_CB(skb)->seq == tcp_sk(sk)->duplicate_sack[0].start_seq) {
		sk_rethink_txhash(sk);
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPDUPLICATEDATAREHASH);
	}
}

static void tcp_send_dupack(struct sock *sk, const struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (TCP_SKB_CB(skb)->end_seq != TCP_SKB_CB(skb)->seq &&
	    before(TCP_SKB_CB(skb)->seq, tp->rcv_nxt)) {
		NET_INC_STATS(sock_net(sk), LINUX_MIB_DELAYEDACKLOST);
		tcp_enter_quickack_mode(sk, TCP_MAX_QUICKACKS);

		if (tcp_is_sack(tp) && sock_net(sk)->ipv4.sysctl_tcp_dsack) {
			u32 end_seq = TCP_SKB_CB(skb)->end_seq;

			tcp_rcv_spurious_retrans(sk, skb);
			if (after(TCP_SKB_CB(skb)->end_seq, tp->rcv_nxt))
				end_seq = tp->rcv_nxt;
			tcp_dsack_set(sk, TCP_SKB_CB(skb)->seq, end_seq);
		}
	}

	tcp_send_ack(sk);
}

/* These routines update the SACK block as out-of-order packets arrive or
 * in-order packets close up the sequence space.
 */
static void tcp_sack_maybe_coalesce(struct tcp_sock *tp)
{
	int this_sack;
	struct tcp_sack_block *sp = &tp->selective_acks[0];
	struct tcp_sack_block *swalk = sp + 1;

	/* See if the recent change to the first SACK eats into
	 * or hits the sequence space of other SACK blocks, if so coalesce.
	 */
	for (this_sack = 1; this_sack < tp->rx_opt.num_sacks;) {
		if (tcp_sack_extend(sp, swalk->start_seq, swalk->end_seq)) {
			int i;

			/* Zap SWALK, by moving every further SACK up by one slot.
			 * Decrease num_sacks.
			 */
			tp->rx_opt.num_sacks--;
			for (i = this_sack; i < tp->rx_opt.num_sacks; i++)
				sp[i] = sp[i + 1];
			continue;
		}
		this_sack++, swalk++;
	}
}

static void tcp_sack_compress_send_ack(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (!tp->compressed_ack)
		return;

	if (hrtimer_try_to_cancel(&tp->compressed_ack_timer) == 1)
		__sock_put(sk);

	/* Since we have to send one ack finally,
	 * substract one from tp->compressed_ack to keep
	 * LINUX_MIB_TCPACKCOMPRESSED accurate.
	 */
	NET_ADD_STATS(sock_net(sk), LINUX_MIB_TCPACKCOMPRESSED,
		      tp->compressed_ack - 1);

	tp->compressed_ack = 0;
	tcp_send_ack(sk);
}

/* Reasonable amount of sack blocks included in TCP SACK option
 * The max is 4, but this becomes 3 if TCP timestamps are there.
 * Given that SACK packets might be lost, be conservative and use 2.
 */
#define TCP_SACK_BLOCKS_EXPECTED 2

static void tcp_sack_new_ofo_skb(struct sock *sk, u32 seq, u32 end_seq)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct tcp_sack_block *sp = &tp->selective_acks[0];
	int cur_sacks = tp->rx_opt.num_sacks;
	int this_sack;

	if (!cur_sacks)
		goto new_sack;

	for (this_sack = 0; this_sack < cur_sacks; this_sack++, sp++) {
		if (tcp_sack_extend(sp, seq, end_seq)) {
			if (this_sack >= TCP_SACK_BLOCKS_EXPECTED)
				tcp_sack_compress_send_ack(sk);
			/* Rotate this_sack to the first one. */
			for (; this_sack > 0; this_sack--, sp--)
				swap(*sp, *(sp - 1));
			if (cur_sacks > 1)
				tcp_sack_maybe_coalesce(tp);
			return;
		}
	}

	if (this_sack >= TCP_SACK_BLOCKS_EXPECTED)
		tcp_sack_compress_send_ack(sk);

	/* Could not find an adjacent existing SACK, build a new one,
	 * put it at the front, and shift everyone else down.  We
	 * always know there is at least one SACK present already here.
	 *
	 * If the sack array is full, forget about the last one.
	 */
	if (this_sack >= TCP_NUM_SACKS) {
		this_sack--;
		tp->rx_opt.num_sacks--;
		sp--;
	}
	for (; this_sack > 0; this_sack--, sp--)
		*sp = *(sp - 1);

new_sack:
	/* Build the new head SACK, and we're done. */
	sp->start_seq = seq;
	sp->end_seq = end_seq;
	tp->rx_opt.num_sacks++;
}

/* RCV.NXT advances, some SACKs should be eaten. */

static void tcp_sack_remove(struct tcp_sock *tp)
{
	struct tcp_sack_block *sp = &tp->selective_acks[0];
	int num_sacks = tp->rx_opt.num_sacks;
	int this_sack;

	/* Empty ofo queue, hence, all the SACKs are eaten. Clear. */
	if (RB_EMPTY_ROOT(&tp->out_of_order_queue)) {
		tp->rx_opt.num_sacks = 0;
		return;
	}

	for (this_sack = 0; this_sack < num_sacks;) {
		/* Check if the start of the sack is covered by RCV.NXT. */
		if (!before(tp->rcv_nxt, sp->start_seq)) {
			int i;

			/* RCV.NXT must cover all the block! */
			WARN_ON(before(tp->rcv_nxt, sp->end_seq));

			/* Zap this SACK, by moving forward any other SACKS. */
			for (i = this_sack+1; i < num_sacks; i++)
				tp->selective_acks[i-1] = tp->selective_acks[i];
			num_sacks--;
			continue;
		}
		this_sack++;
		sp++;
	}
	tp->rx_opt.num_sacks = num_sacks;
}

/**
 * tcp_try_coalesce - try to merge skb to prior one
 * @sk: socket
 * @dest: destination queue
 * @to: prior buffer
 * @from: buffer to add in queue
 * @fragstolen: pointer to boolean
 *
 * Before queueing skb @from after @to, try to merge them
 * to reduce overall memory use and queue lengths, if cost is small.
 * Packets in ofo or receive queues can stay a long time.
 * Better try to coalesce them right now to avoid future collapses.
 * Returns true if caller should free @from instead of queueing it
 */
static bool tcp_try_coalesce(struct sock *sk,
			     struct sk_buff *to,
			     struct sk_buff *from,
			     bool *fragstolen)
{
	int delta;

	*fragstolen = false;

	/* Its possible this segment overlaps with prior segment in queue */
    /* 序号对不上 */
	if (TCP_SKB_CB(from)->seq != TCP_SKB_CB(to)->end_seq)
		return false;

	if (!mptcp_skb_can_collapse(to, from))
		return false;

#ifdef CONFIG_TLS_DEVICE
	if (from->decrypted != to->decrypted)
		return false;
#endif

    /* 尝试合并到前一个数据段 */
	if (!skb_try_coalesce(to, from, fragstolen, &delta))
		return false;

    /* 调整内存使用 */
	atomic_add(delta, &sk->sk_rmem_alloc);
	sk_mem_charge(sk, delta);
	NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPRCVCOALESCE);
    /* 更新cb相关字段 */
	TCP_SKB_CB(to)->end_seq = TCP_SKB_CB(from)->end_seq;
	TCP_SKB_CB(to)->ack_seq = TCP_SKB_CB(from)->ack_seq;
	TCP_SKB_CB(to)->tcp_flags |= TCP_SKB_CB(from)->tcp_flags;

	if (TCP_SKB_CB(from)->has_rxtstamp) {
		TCP_SKB_CB(to)->has_rxtstamp = true;
		to->tstamp = from->tstamp;
		skb_hwtstamps(to)->hwtstamp = skb_hwtstamps(from)->hwtstamp;
	}

	return true;
}

static bool tcp_ooo_try_coalesce(struct sock *sk,
			     struct sk_buff *to,
			     struct sk_buff *from,
			     bool *fragstolen)
{
	bool res = tcp_try_coalesce(sk, to, from, fragstolen);

	/* In case tcp_drop() is called later, update to->gso_segs */
	if (res) {
		u32 gso_segs = max_t(u16, 1, skb_shinfo(to)->gso_segs) +
			       max_t(u16, 1, skb_shinfo(from)->gso_segs);

		skb_shinfo(to)->gso_segs = min_t(u32, gso_segs, 0xFFFF);
	}
	return res;
}

static void tcp_drop(struct sock *sk, struct sk_buff *skb)
{
	sk_drops_add(sk, skb);
	__kfree_skb(skb);
}

/* This one checks to see if we can put data from the
 * out_of_order queue into the receive_queue.
 */
static void tcp_ofo_queue(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	__u32 dsack_high = tp->rcv_nxt;
	bool fin, fragstolen, eaten;
	struct sk_buff *skb, *tail;
	struct rb_node *p;

	p = rb_first(&tp->out_of_order_queue);
	while (p) {
		skb = rb_to_skb(p);
        /* 当前hole未覆盖，则处理结束 */
		if (after(TCP_SKB_CB(skb)->seq, tp->rcv_nxt))
			break;

        /* DSACK处理 */
		if (before(TCP_SKB_CB(skb)->seq, dsack_high)) {
			__u32 dsack = dsack_high;
			if (before(TCP_SKB_CB(skb)->end_seq, dsack_high))
				dsack_high = TCP_SKB_CB(skb)->end_seq;
			tcp_dsack_extend(sk, TCP_SKB_CB(skb)->seq, dsack);
		}
		p = rb_next(p);
		rb_erase(&skb->rbnode, &tp->out_of_order_queue);

        /* 该乱序数据包完全被到达的数据包覆盖，则从乱序队列中删除之，并释放该数据包 */
		if (unlikely(!after(TCP_SKB_CB(skb)->end_seq, tp->rcv_nxt))) {
			tcp_drop(sk, skb);
			continue;
		}

        /* hole被填充，取出该乱序数据包到receive queue中排队，并更新rcv_nxt */
		tail = skb_peek_tail(&sk->sk_receive_queue);
		// 尝试将sk_receive_queue接收队列的最后一个数据包tail与节点数据包skb进行合并tcp_try_coalesce
		// fragstolen表示合并了数据包的线性缓存部分的数据，但是共享缓存中的数据继续在使用，所以不能够释放
		eaten = tail && tcp_try_coalesce(sk, tail, skb, &fragstolen);
		tcp_rcv_nxt_update(tp, TCP_SKB_CB(skb)->end_seq);
		fin = TCP_SKB_CB(skb)->tcp_flags & TCPHDR_FIN;
		if (!eaten)
		    // 合并失败，将节点的skb添加到sk_receive_queue队列的末尾。
			__skb_queue_tail(&sk->sk_receive_queue, skb);
		else
		    // 合并成功，调用kfree_skb_partial释放skb
			kfree_skb_partial(skb, fragstolen);

		if (unlikely(fin)) {
		    // 节点数据包带有TCP的FIN标志，调用tcp_fin函数处理，在其中将清空out_of_order_queue队列
			tcp_fin(sk);
			/* tcp_fin() purges tp->out_of_order_queue,
			 * so we must end this loop right now.
			 */
			break;
		}
	}
}

static bool tcp_prune_ofo_queue(struct sock *sk);
static int tcp_prune_queue(struct sock *sk);

static int tcp_try_rmem_schedule(struct sock *sk, struct sk_buff *skb,
				 unsigned int size)
{
	if (atomic_read(&sk->sk_rmem_alloc) > sk->sk_rcvbuf || // 接收缓存分配超量
	    !sk_rmem_schedule(sk, skb, size)) {     // 全局缓存或接收缓存空间达到上限

		if (tcp_prune_queue(sk) < 0) // 释放一部分缓存，必要时会清空乱序队列
			return -1;

		while (!sk_rmem_schedule(sk, skb, size)) { // 经过释放后仍然超限
			if (!tcp_prune_ofo_queue(sk)) // 清除乱序队列中所有的包
				return -1;
		}
	}
	return 0;
}

static void tcp_data_queue_ofo(struct sock *sk, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct rb_node **p, *parent;
	struct sk_buff *skb1;
	u32 seq, end_seq;
	bool fragstolen;

	tcp_ecn_check_ce(sk, skb); /* 检查ECE是否设置 */

    /* 以下则把数据包排队到乱序队列 */

    /* 先判断内存是否满足 */
	if (unlikely(tcp_try_rmem_schedule(sk, skb, skb->truesize))) {
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPOFODROP);
		sk->sk_data_ready(sk);
		tcp_drop(sk, skb);
		return;
	}

	/* Disable header prediction. */
	tp->pred_flags = 0;
	// 标识此socket正在等待发送ACK，如果以后有数据要发送的话会尽快发送，以便将携带的ACK尽快发送到对端
	inet_csk_schedule_ack(sk);

	tp->rcv_ooopack += max_t(u16, 1, skb_shinfo(skb)->gso_segs);
	NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPOFOQUEUE);
	seq = TCP_SKB_CB(skb)->seq;
	end_seq = TCP_SKB_CB(skb)->end_seq;

	p = &tp->out_of_order_queue.rb_node;
    /* 该数据包是乱序队列的第一个数据包 */
	if (RB_EMPTY_ROOT(&tp->out_of_order_queue)) { // 乱序队列中没有数据
		/* Initial out of order segment, build 1 SACK. */
		if (tcp_is_sack(tp)) {
            // 套接口连接支持SACK，使用乱序数据包的起始和结束序列号初始化一个SACK块
			tp->rx_opt.num_sacks = 1;
			tp->selective_acks[0].start_seq = seq;
			tp->selective_acks[0].end_seq = end_seq;
		}
		// 将skb放入乱序队列中
		rb_link_node(&skb->rbnode, NULL, p);
		rb_insert_color(&skb->rbnode, &tp->out_of_order_queue);
		tp->ooo_last_skb = skb;
		goto end;
	}

	/* In the typical case, we are adding an skb to the end of the list.
	 * Use of ooo_last_skb avoids the O(Log(N)) rbtree lookup.
	 * 接收skb数据包的开始序号等于队列中最后一个数据包的结束序号，将skb合并到队列最后的数据包中
	 */
	if (tcp_ooo_try_coalesce(sk, tp->ooo_last_skb,
				 skb, &fragstolen)) {
coalesce_done:
		/* For non sack flows, do not grow window to force DUPACK
		 * and trigger fast retransmit.
		 */
		if (tcp_is_sack(tp))
			tcp_grow_window(sk, skb);
		kfree_skb_partial(skb, fragstolen);
		skb = NULL;
		goto add_sack;
	}
	/* Can avoid an rbtree lookup if we are adding skb after ooo_last_skb
	 * 接收skb数据包的开始序位于队列最后一个数据包的结束序号之后，将skb插入到最后数据包所在红黑树节点的右侧
	 */
	if (!before(seq, TCP_SKB_CB(tp->ooo_last_skb)->end_seq)) {
		parent = &tp->ooo_last_skb->rbnode;
		p = &parent->rb_right;
		goto insert;
	}

	/* Find place to insert this segment. Handle overlaps on the way. */
	// 遍历红黑树，查找数据包的插入位置
	parent = NULL;
	while (*p) {
		parent = *p;
		skb1 = rb_to_skb(parent);
		if (before(seq, TCP_SKB_CB(skb1)->seq)) {// 数据包开始序号位于节点数据包开始序号的之前，向树的左侧遍历
			p = &parent->rb_left;
			continue;
		}
		if (before(seq, TCP_SKB_CB(skb1)->end_seq)) {
			if (!after(end_seq, TCP_SKB_CB(skb1)->end_seq)) {/* 数据包的开始序号位于节点数据包的结束序号之前，
                                                * 并且数据包的结束序号位于节点数据包的结束序号之前，
                                                * 说明节点数据包包含有此接收数据包，不执行插入，
                                                * 设置套接口的重复SACK块，跳出遍历
                                                */
				/* All the bits are present. Drop. */
				NET_INC_STATS(sock_net(sk),
					      LINUX_MIB_TCPOFOMERGE);
				tcp_drop(sk, skb);
				skb = NULL;
				tcp_dsack_set(sk, seq, end_seq);
				goto add_sack;
			}
			if (after(seq, TCP_SKB_CB(skb1)->seq)) {/* 数据包的开始序号位于节点数据包的结束序号之前，
                                                * 并且数据包的开始序号位于节点数据包的开始序号之后，
                                                * 并且结束序号位于节点数据包结束序号之后
                                                * 并且数据包的开始序号位于节点数据包的开始序号之后，
                                                * 表明两个数据包有部分数据重叠，
                                                * 内核使用接收数据包的开始序号和节点数据包的结束序号设置套接口的重复SACK块，
                                                * 继续遍历知道队列结束或者其它情况发生，
                                                * 所以在out_of_order_queue树中的数据包由可能存在部分重叠的情况。
                                                */
				/* Partial overlap. */
				tcp_dsack_set(sk, seq, TCP_SKB_CB(skb1)->end_seq);
			} else { /* 接收数据包的开始序号与节点数据包的开始序号相同，
                      * 并且其结束序号位于节点数据包的结束序号之后，即接收数据包完全包含节点数据包，
                      * 使用新接收数据包替换掉树中的节点数据包，调用函数tcp_dsack_extend扩展套接口SACK设置，
                      * 跳出遍历
                      */
				/* skb's seq == skb1's seq and skb covers skb1.
				 * Replace skb1 with skb.
				 */
				rb_replace_node(&skb1->rbnode, &skb->rbnode,
						&tp->out_of_order_queue);
				tcp_dsack_extend(sk,
						 TCP_SKB_CB(skb1)->seq,
						 TCP_SKB_CB(skb1)->end_seq);
				NET_INC_STATS(sock_net(sk),
					      LINUX_MIB_TCPOFOMERGE);
				tcp_drop(sk, skb1);
				goto merge_right;
			}
		} else if (tcp_ooo_try_coalesce(sk, skb1,
						skb, &fragstolen)) {/* 接收数据包的开始序号位于节点开始序号和结束序号之后，
                                         * 内核调用函数tcp_try_coalesce尝试将接收数据包合并到节点数据包中。
                                         */
			goto coalesce_done;
		}
		p = &parent->rb_right;
	}
insert:
	/* Insert segment into RB tree. */
	rb_link_node(&skb->rbnode, parent, p);
	rb_insert_color(&skb->rbnode, &tp->out_of_order_queue);

merge_right:
	/* Remove other segments covered by skb. */
	// 插入完成之后，需要遍历skb节点之后的其它节点，以检查是否有其它节点位置的数据包被本数据包所覆盖
	while ((skb1 = skb_rb_next(skb)) != NULL) {
		if (!after(end_seq, TCP_SKB_CB(skb1)->seq)) //没有覆盖，直接跳出循环
			break;
		if (before(end_seq, TCP_SKB_CB(skb1)->end_seq)) { // 只是部分重叠，仅做SACK扩展
			tcp_dsack_extend(sk, TCP_SKB_CB(skb1)->seq,
					 end_seq);
			break;
		}
		// 如果有覆盖，内核将擦除被覆盖的节点，并且释放节点数据包，调用函数tcp_dsack_extend扩展套接口SACK设置。
		rb_erase(&skb1->rbnode, &tp->out_of_order_queue);
		tcp_dsack_extend(sk, TCP_SKB_CB(skb1)->seq,
				 TCP_SKB_CB(skb1)->end_seq);
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPOFOMERGE);
		tcp_drop(sk, skb1);
	}
	/* If there is no skb after us, we are the last_skb ! */
	// 如果数据包skb为最后一个树节点，更新ooo_last_skb指针
	if (!skb1)
		tp->ooo_last_skb = skb;

add_sack:
	if (tcp_is_sack(tp))
        /* 根据乱序队列的现状更新SACK的blocks */
		tcp_sack_new_ofo_skb(sk, seq, end_seq);
end:
	if (skb) {
		/* For non sack flows, do not grow window to force DUPACK
		 * and trigger fast retransmit.
		 */
		if (tcp_is_sack(tp))
			tcp_grow_window(sk, skb);
		skb_condense(skb);
		skb_set_owner_r(skb, sk);
	}
}
// tcp_queue_rcv用于将接收到的skb加入到接收队列receive_queue中，
// 首先会调用tcp_try_coalesce进行分段合并到队列中最后一个skb的尝试，
// 若失败则调用__skb_queue_tail添加该skb到队列尾部；
static int __must_check tcp_queue_rcv(struct sock *sk, struct sk_buff *skb,
				      bool *fragstolen)
{
	int eaten;
    /* 取队尾 */
	struct sk_buff *tail = skb_peek_tail(&sk->sk_receive_queue);

    /* 尝试进行分段合并 */
	eaten = (tail &&
		 tcp_try_coalesce(sk, tail,
				  skb, fragstolen)) ? 1 : 0;
    /* 更新下一个期望接收的序号 */
	tcp_rcv_nxt_update(tcp_sk(sk), TCP_SKB_CB(skb)->end_seq);
    /* 未合并 */
	if (!eaten) {
        /* 添加到队列尾部 */
		__skb_queue_tail(&sk->sk_receive_queue, skb);
        /* 关联控制块 */
		skb_set_owner_r(skb, sk);
	}
	return eaten;
}

int tcp_send_rcvq(struct sock *sk, struct msghdr *msg, size_t size)
{
	struct sk_buff *skb;
	int err = -ENOMEM;
	int data_len = 0;
	bool fragstolen;

	if (size == 0)
		return 0;

	if (size > PAGE_SIZE) {
		int npages = min_t(size_t, size >> PAGE_SHIFT, MAX_SKB_FRAGS);

		data_len = npages << PAGE_SHIFT;
		size = data_len + (size & ~PAGE_MASK);
	}
	skb = alloc_skb_with_frags(size - data_len, data_len,
				   PAGE_ALLOC_COSTLY_ORDER,
				   &err, sk->sk_allocation);
	if (!skb)
		goto err;

	skb_put(skb, size - data_len);
	skb->data_len = data_len;
	skb->len = size;

	if (tcp_try_rmem_schedule(sk, skb, skb->truesize)) {
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPRCVQDROP);
		goto err_free;
	}

	err = skb_copy_datagram_from_iter(skb, 0, &msg->msg_iter, size);
	if (err)
		goto err_free;

	TCP_SKB_CB(skb)->seq = tcp_sk(sk)->rcv_nxt;
	TCP_SKB_CB(skb)->end_seq = TCP_SKB_CB(skb)->seq + size;
	TCP_SKB_CB(skb)->ack_seq = tcp_sk(sk)->snd_una - 1;

	if (tcp_queue_rcv(sk, skb, &fragstolen)) {
		WARN_ON_ONCE(fragstolen); /* should not happen */
		__kfree_skb(skb);
	}
	return size;

err_free:
	kfree_skb(skb);
err:
	return err;

}

void tcp_data_ready(struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);
	int avail = tp->rcv_nxt - tp->copied_seq;

	if (avail < sk->sk_rcvlowat && !tcp_rmem_pressure(sk) &&
	    !sock_flag(sk, SOCK_DONE))
		return;

	sk->sk_data_ready(sk);
}
/*
 * 第一种情况，seq == tp->rcv_nxt，说明来的网络包正是我服务端期望的下一个网络包。
 * 调用 sock_owned_by_user()判断用户进程是否正在等待读取，如果是则直接调用 skb_copy_datagram_msg()，
 * 将网络包拷贝给用户进程就可以了。如果用户进程没有正在等待读取，或者因为内存原因没有能够拷贝成功，
 * tcp_queue_rcv() 里面还是将网络包放入 sk_receive_queue 队列。
 * 调用tcp_rcv_nxt_update() 将 tp->rcv_nxt 设置为 end_seq，也即当前的网络包接收成功后，更新下一个期待的网络包
 * 判断一下另一个队列out_of_order_queue，即乱序队列的情况，看看乱序队列里面的包会不会因为这个新的网络包的到来，
 * 也能放入到 sk_receive_queue 队列中。
 * 第二种情况，end_seq 小于 rcv_nxt，也即服务端期望网络包 5。但是，来了一个网络包 3，怎样才会出现这种情况呢？肯定是服务端早就收到了网络包 3，但是 ACK 没有到达客户端，中途丢了，那客户端就认为网络包 3 没有发送成功，于是又发送了一遍，这种情况下，要赶紧给客户端再发送一次 ACK，表示早就收到了。
 * 第三种情况，seq 大于 rcv_nxt + tcp_receive_window。这说明客户端发送得太猛了。本来 seq 肯定应该在接收窗口里面的，这样服务端才来得及处理，结果现在超出了接收窗口，说明客户端一下子把服务端给塞满了。这种情况下，服务端不能再接收数据包了，只能发送 ACK 了，在 ACK 中会将接收窗口为 0 的情况告知客户端，客户端就知道不能再发送了。这个时候双方只能交互窗口探测数据包，直到服务端因为用户进程把数据读走了，空出接收窗口，才能在 ACK 里面再次告诉客户端，又有窗口了，又能发送数据包了。
 * 第四种情况，seq 小于 rcv_nxt，但是 end_seq 大于 rcv_nxt，这说明从 seq 到 rcv_nxt 这部分网络包原来的 ACK 客户端没有收到，所以重新发送了一次，从 rcv_nxt 到 end_seq 是新发送的，可以放入 sk_receive_queue 队列。
 * 第五种情况，是正好在接收窗口内但是不是期望接收的下一个包，则说明发生了乱序，调用tcp_data_queue_ofo()加入乱序队列中。
 */
static void tcp_data_queue(struct sock *sk, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	bool fragstolen;
	int eaten;

	if (sk_is_mptcp(sk))
		mptcp_incoming_options(sk, skb, &tp->rx_opt);

    /* 没有数据处理*/
	if (TCP_SKB_CB(skb)->seq == TCP_SKB_CB(skb)->end_seq) {
		__kfree_skb(skb);
		return;
	}
    /* 删除路由缓存 */
	skb_dst_drop(skb);
    /* 跳过tcp头部 */
	__skb_pull(skb, tcp_hdr(skb)->doff * 4);

	tp->rx_opt.dsack = 0;

	/*  Queue data for delivery to the user.
	 *  Packets in sequence go to the receive queue.
	 *  Out of sequence packets to the out_of_order_queue.
	 */
    /* 预期接收的数据段 */
	if (TCP_SKB_CB(skb)->seq == tp->rcv_nxt) {
        /* 窗口为0，不能接收数据 */
		if (tcp_receive_window(tp) == 0) {
			NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPZEROWINDOWDROP);
			goto out_of_window;
		}

		/* Ok. In sequence. In window. */
        /* 进程上下文 */
queue_and_out:
		if (skb_queue_len(&sk->sk_receive_queue) == 0) // sk_receive_queue没有数据
			sk_forced_mem_schedule(sk, skb->truesize); // 检查是否需要分配配额
		else if (tcp_try_rmem_schedule(sk, skb, skb->truesize)) { // 查看接收缓存空间够不够
			NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPRCVQDROP);
			sk->sk_data_ready(sk);
			goto drop;
		}

        /* 添加到接收队列 */
		eaten = tcp_queue_rcv(sk, skb, &fragstolen);
        /* 有数据 */
		if (skb->len)
			tcp_event_data_recv(sk, skb);
        /* 标记有fin，则处理 */
		if (TCP_SKB_CB(skb)->tcp_flags & TCPHDR_FIN)
			tcp_fin(sk);

        /* 乱序队列有数据，则处理 */
		if (!RB_EMPTY_ROOT(&tp->out_of_order_queue)) {
            /* 将乱序队列中的数据段转移到接收队列
             * 调用函数tcp_ofo_queue检查out_of_order_queue队列中是否有数据包可用。
             * 即新接收的数据包添上了套接口下一个接收序号与out_of_order_queue队列中数据包序号之间的空缺，
             * 使out_of_order_queue中的部分数据包变成序号连续的可用数据包。
             * 如果以上成立的话，内核将马上发送ACK确认报文，以通知对端新的请求数据包序号
             */
			tcp_ofo_queue(sk);

			/* RFC5681. 4.2. SHOULD send immediate ACK, when
			 * gap in queue is filled.
			 */
            /* 乱序数据段处理完毕，需要立即发送ack */
			if (RB_EMPTY_ROOT(&tp->out_of_order_queue))
				inet_csk(sk)->icsk_ack.pending |= ICSK_ACK_NOW;
		}

		if (tp->rx_opt.num_sacks)
			tcp_sack_remove(tp);

		// 处理包的快速path 检查。如果支持快速处理就在此置位
		tcp_fast_path_check(sk);

        /* 向用户空间拷贝了数据，则释放skb */
		if (eaten > 0)
			kfree_skb_partial(skb, fragstolen);
        /* 不在销毁状态，则唤醒进程读取数据 */
		if (!sock_flag(sk, SOCK_DEAD))
			tcp_data_ready(sk);
		return;
	}

    /* 重传ack */
    /* 该数据包的数据已经完全存在，则发送 DSACK，并进入快速 ACK 模式，调度 ACK 发送
     *
     * end_seq 小于 rcv_nxt，也即服务端期望网络包 5。
     * 但是，来了一个网络包 3，怎样才会出现这种情况呢？
     * 肯定是服务端早就收到了网络包 3，但是 ACK 没有到达客户端，中途丢了，那客户端就认为网络包 3 没有发送成功，
     * 于是又发送了一遍，这种情况下，要赶紧给客户端再发送一次 ACK，表示早就收到了。
     */
	if (!after(TCP_SKB_CB(skb)->end_seq, tp->rcv_nxt)) {
		tcp_rcv_spurious_retrans(sk, skb);
		/* A retransmit, 2nd most common case.  Force an immediate ack. */
		NET_INC_STATS(sock_net(sk), LINUX_MIB_DELAYEDACKLOST);
		tcp_dsack_set(sk, TCP_SKB_CB(skb)->seq, TCP_SKB_CB(skb)->end_seq);

out_of_window:
        /* 进入快速ack模式 */
		tcp_enter_quickack_mode(sk, TCP_MAX_QUICKACKS);
        /*  调度ack */
		inet_csk_schedule_ack(sk);
drop:
        /* 释放skb */
		tcp_drop(sk, skb);
		return;
	}

	/* Out of window. F.e. zero window probe. */
    /* 窗口以外的数据，比如零窗口探测报文段 */
    /*
     * seq 大于 rcv_nxt + tcp_receive_window。这说明客户端发送得太猛了。
     * 本来 seq 肯定应该在接收窗口里面的，这样服务端才来得及处理，结果现在超出了接收窗口，
     * 说明客户端一下子把服务端给塞满了。这种情况下，服务端不能再接收数据包了，
     * 只能发送 ACK 了，在 ACK 中会将接收窗口为 0 的情况告知客户端，客户端就知道不能再发送了。
     * 这个时候双方只能交互窗口探测数据包，直到服务端因为用户进程把数据读走了，空出接收窗口，
     * 才能在 ACK 里面再次告诉客户端，又有窗口了，又能发送数据包了。
     */
	if (!before(TCP_SKB_CB(skb)->seq, tp->rcv_nxt + tcp_receive_window(tp)))
		goto out_of_window;

    /* 数据段重叠 */
    /*
     * seq 小于 rcv_nxt，但是 end_seq 大于 rcv_nxt，
     * 这说明从 seq 到 rcv_nxt 这部分网络包原来的 ACK 客户端没有收到，
     * 所以重新发送了一次，从 rcv_nxt 到 end_seq 是新发送的，可以放入 sk_receive_queue 队列。
     */
	if (before(TCP_SKB_CB(skb)->seq, tp->rcv_nxt)) {
		/* Partial packet, seq < rcv_next < end_seq */
		tcp_dsack_set(sk, TCP_SKB_CB(skb)->seq, tp->rcv_nxt);

		/* If window is closed, drop tail of packet. But after
		 * remembering D-SACK for its head made in previous line.
		 */
        /* 窗口为0，不能接收 */
		if (!tcp_receive_window(tp)) {
			NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPZEROWINDOWDROP);
			goto out_of_window;
		}
		goto queue_and_out;
	}

	// 乱序处理
	/*
	 * 正好在接收窗口内但是不是期望接收的下一个包，则说明发生了乱序，调用tcp_data_queue_ofo()加入乱序队列中。
	 */
	tcp_data_queue_ofo(sk, skb);
}

static struct sk_buff *tcp_skb_next(struct sk_buff *skb, struct sk_buff_head *list)
{
	if (list)
		return !skb_queue_is_last(list, skb) ? skb->next : NULL;

	return skb_rb_next(skb);
}

static struct sk_buff *tcp_collapse_one(struct sock *sk, struct sk_buff *skb,
					struct sk_buff_head *list,
					struct rb_root *root)
{
	struct sk_buff *next = tcp_skb_next(skb, list);

	if (list)
		__skb_unlink(skb, list);
	else
		rb_erase(&skb->rbnode, root);

	__kfree_skb(skb);
	NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPRCVCOLLAPSED);

	return next;
}

/* Insert skb into rb tree, ordered by TCP_SKB_CB(skb)->seq */
void tcp_rbtree_insert(struct rb_root *root, struct sk_buff *skb)
{
	struct rb_node **p = &root->rb_node;
	struct rb_node *parent = NULL;
	struct sk_buff *skb1;

	while (*p) {
		parent = *p;
		skb1 = rb_to_skb(parent);
		if (before(TCP_SKB_CB(skb)->seq, TCP_SKB_CB(skb1)->seq))
			p = &parent->rb_left;
		else
			p = &parent->rb_right;
	}
	rb_link_node(&skb->rbnode, parent, p);
	rb_insert_color(&skb->rbnode, root);
}

/* Collapse contiguous sequence of skbs head..tail with
 * sequence numbers start..end.
 *
 * If tail is NULL, this means until the end of the queue.
 *
 * Segments with FIN/SYN are not collapsed (only because this
 * simplifies code)
 */
static void
tcp_collapse(struct sock *sk, struct sk_buff_head *list, struct rb_root *root,
	     struct sk_buff *head, struct sk_buff *tail, u32 start, u32 end)
{
	struct sk_buff *skb = head, *n;
	struct sk_buff_head tmp;
	bool end_of_skbs;

	/* First, check that queue is collapsible and find
	 * the point where collapsing can be useful.
	 */
restart:
	for (end_of_skbs = true; skb != NULL && skb != tail; skb = n) {
		n = tcp_skb_next(skb, list);

		/* No new bits? It is possible on ofo queue. */
        // 要求折叠的start开始序号在当前遍历数据包skb的接收序号之后，
        // 说明此数据包已被包括在内，不在需要了，使用tcp_collapse_one清除此数据包
		if (!before(start, TCP_SKB_CB(skb)->end_seq)) {
			skb = tcp_collapse_one(sk, skb, list, root);
			if (!skb)
				break;
			goto restart;
		}

		/* The first skb to collapse is:
		 * - not SYN/FIN and
		 * - bloated or contains data before "start" or
		 *   overlaps to the next one and mptcp allow collapsing.
		 */
		// skb数据的TCP头部未设置SYN或者FIN标志，
		// 并且由数据包的truesize长度计算的窗口值大于数据包的数据长度，
		// 或者数据包的开始序号在start之前，即找到进行折叠的开始数据包
		if (!(TCP_SKB_CB(skb)->tcp_flags & (TCPHDR_SYN | TCPHDR_FIN)) &&
		    (tcp_win_from_space(sk, skb->truesize) > skb->len ||
		     before(TCP_SKB_CB(skb)->seq, start))) {
			end_of_skbs = false;
			break;
		}

		// skb的下一个树节点不是末尾节点，并且skb的结束序号不等于下一个树节点的开始序号，
		// 两者有重叠，将此skb做为折叠开始节点
		if (n && n != tail && mptcp_skb_can_collapse(skb, n) &&
		    TCP_SKB_CB(skb)->end_seq != TCP_SKB_CB(n)->seq) {
			end_of_skbs = false;
			break;
		}

		/* Decided to skip this, advance start seq. */
		start = TCP_SKB_CB(skb)->end_seq;
	}
	if (end_of_skbs ||
	    (TCP_SKB_CB(skb)->tcp_flags & (TCPHDR_SYN | TCPHDR_FIN)))
		return;

	// 进行折叠操作
	__skb_queue_head_init(&tmp);

	// 宏SKB_MAX_ORDER（0,0）的结果为页面大小减去skb_shared_info结构体的长度所得到的值。
    // #define SKB_WITH_OVERHEAD(X)     ((X) - SKB_DATA_ALIGN(sizeof(struct skb_shared_info)))
    // #define SKB_MAX_ORDER(X, ORDER)  SKB_WITH_OVERHEAD((PAGE_SIZE << (ORDER)) - (X))

	while (before(start, end)) {
		int copy = min_t(int, SKB_MAX_ORDER(0, 0), end - start);
		struct sk_buff *nskb;

		nskb = alloc_skb(copy, GFP_ATOMIC);
		if (!nskb)
			break;

		memcpy(nskb->cb, skb->cb, sizeof(skb->cb));
#ifdef CONFIG_TLS_DEVICE
		nskb->decrypted = skb->decrypted;
#endif
		TCP_SKB_CB(nskb)->seq = TCP_SKB_CB(nskb)->end_seq = start;
		if (list)
			__skb_queue_before(list, skb, nskb);
		else
			__skb_queue_tail(&tmp, nskb); /* defer rbtree insertion */
		skb_set_owner_r(nskb, sk);
		mptcp_skb_ext_move(nskb, skb);

		/* Copy data, releasing collapsed skbs. */
		while (copy > 0) {
			int offset = start - TCP_SKB_CB(skb)->seq;
			int size = TCP_SKB_CB(skb)->end_seq - start;

			BUG_ON(offset < 0);
			if (size > 0) {
				size = min(copy, size);
				if (skb_copy_bits(skb, offset, skb_put(nskb, size), size))
					BUG();
				TCP_SKB_CB(nskb)->end_seq += size;
				copy -= size;
				start += size;
			}
			if (!before(start, TCP_SKB_CB(skb)->end_seq)) {
				skb = tcp_collapse_one(sk, skb, list, root);
				if (!skb ||
				    skb == tail ||
				    !mptcp_skb_can_collapse(nskb, skb) ||
				    (TCP_SKB_CB(skb)->tcp_flags & (TCPHDR_SYN | TCPHDR_FIN)))
					goto end;
#ifdef CONFIG_TLS_DEVICE
				if (skb->decrypted != nskb->decrypted)
					goto end;
#endif
			}
		}
	}
end:
	skb_queue_walk_safe(&tmp, skb, n)
		tcp_rbtree_insert(root, skb);
}

/* Collapse ofo queue. Algorithm: select contiguous sequence of skbs
 * and tcp_collapse() them until all the queue is collapsed.
 */
static void tcp_collapse_ofo_queue(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 range_truesize, sum_tiny = 0;
	struct sk_buff *skb, *head;
	u32 start, end;

	skb = skb_rb_first(&tp->out_of_order_queue);
new_range:
	if (!skb) {
		tp->ooo_last_skb = skb_rb_last(&tp->out_of_order_queue);
		return;
	}
	start = TCP_SKB_CB(skb)->seq;
	end = TCP_SKB_CB(skb)->end_seq;
	range_truesize = skb->truesize;

	for (head = skb;;) {
		skb = skb_rb_next(skb);

		/* Range is terminated when we see a gap or when
		 * we are at the queue end.
		 * 一旦遇到缺口或者队列结尾，标志着此段连续序号数据包的结束，就将这段节点数据进行合并
		 */
		if (!skb ||
		    after(TCP_SKB_CB(skb)->seq, end) ||
		    before(TCP_SKB_CB(skb)->end_seq, start)) {
			/* Do not attempt collapsing tiny skbs */
			if (range_truesize != head->truesize ||
			    end - start >= SKB_WITH_OVERHEAD(SK_MEM_QUANTUM)) {
				tcp_collapse(sk, NULL, &tp->out_of_order_queue,
					     head, skb, start, end);
			} else {
				sum_tiny += range_truesize;
				if (sum_tiny > sk->sk_rcvbuf >> 3)
					return;
			}
			goto new_range;
		}

		// 下一个节点与上一个阶段的序号有重叠
		range_truesize += skb->truesize;
		if (unlikely(before(TCP_SKB_CB(skb)->seq, start)))
		    // 下一个节点的开始序号位于start段开始序号之前，更新start的值
			start = TCP_SKB_CB(skb)->seq;
		if (after(TCP_SKB_CB(skb)->end_seq, end))
		    // 下一个节点的结束序号在end段结束序号之后，更新end的值
			end = TCP_SKB_CB(skb)->end_seq;
	}
}

/*
 * Clean the out-of-order queue to make room.
 * We drop high sequences packets to :
 * 1) Let a chance for holes to be filled.
 * 2) not add too big latencies if thousands of packets sit there.
 *    (But if application shrinks SO_RCVBUF, we could still end up
 *     freeing whole queue here)
 * 3) Drop at least 12.5 % of sk_rcvbuf to avoid malicious attacks.
 *
 * Return true if queue has shrunk.
 * 由out_of_order_queue树的最后一个节点开始遍历树结构，释放树节点，
 * 直到套接口的接收缓存sk_rmem_alloc小于等于设定的接收缓存限值sk_rcvbuf，
 * 并且TCP协议的缓存状态不再处于承压状态为止。此遍历将先释放尾部大序号的数据包，
 * 此举可为小序号数据包的接收腾出空间，以便其组成可供应用层读取的正常数据包
 */
static bool tcp_prune_ofo_queue(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct rb_node *node, *prev;
	int goal;

	if (RB_EMPTY_ROOT(&tp->out_of_order_queue))
		return false;

	NET_INC_STATS(sock_net(sk), LINUX_MIB_OFOPRUNED);
	goal = sk->sk_rcvbuf >> 3;
	node = &tp->ooo_last_skb->rbnode;
	do {
		prev = rb_prev(node);
		rb_erase(node, &tp->out_of_order_queue);
		goal -= rb_to_skb(node)->truesize;
		tcp_drop(sk, rb_to_skb(node));
		if (!prev || goal <= 0) {
			sk_mem_reclaim(sk);
			if (atomic_read(&sk->sk_rmem_alloc) <= sk->sk_rcvbuf &&
			    !tcp_under_memory_pressure(sk))
				break;
			goal = sk->sk_rcvbuf >> 3;
		}
		node = prev;
	} while (node);
	tp->ooo_last_skb = rb_to_skb(prev);

	/* Reset SACK state.  A conforming SACK implementation will
	 * do the same at a timeout based retransmit.  When a connection
	 * is in a sad state like this, we care only about integrity
	 * of the connection not performance.
	 */
	if (tp->rx_opt.sack_ok)
		tcp_sack_reset(&tp->rx_opt);
	return true;
}

/* Reduce allocated memory if we can, trying to get
 * the socket within its memory limits again.
 *
 * Return less than zero if we should start dropping frames
 * until the socket owning process reads some of the data
 * to stabilize the situation.
 */
static int tcp_prune_queue(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	NET_INC_STATS(sock_net(sk), LINUX_MIB_PRUNECALLED);

	if (atomic_read(&sk->sk_rmem_alloc) >= sk->sk_rcvbuf)
		tcp_clamp_window(sk);
	else if (tcp_under_memory_pressure(sk))
		tp->rcv_ssthresh = min(tp->rcv_ssthresh, 4U * tp->advmss);

	if (atomic_read(&sk->sk_rmem_alloc) <= sk->sk_rcvbuf)
		return 0;

	tcp_collapse_ofo_queue(sk); // 尝试合并out_of_order_queue队列中的重复数据
	if (!skb_queue_empty(&sk->sk_receive_queue))
	    // 尝试将sk_receive_queue队列中的数据折叠到少量的skb结构中
		tcp_collapse(sk, &sk->sk_receive_queue, NULL,
			     skb_peek(&sk->sk_receive_queue),
			     NULL,
			     tp->copied_seq, tp->rcv_nxt);
	sk_mem_reclaim(sk);

	if (atomic_read(&sk->sk_rmem_alloc) <= sk->sk_rcvbuf)
		return 0;

	/* Collapsing did not help, destructive actions follow.
	 * This must not ever occur. */

	tcp_prune_ofo_queue(sk); // 删除out_of_order_queue队列中的数据包

	if (atomic_read(&sk->sk_rmem_alloc) <= sk->sk_rcvbuf)
		return 0;

	/* If we are really being abused, tell the caller to silently
	 * drop receive data on the floor.  It will get retransmitted
	 * and hopefully then we'll have sufficient space.
	 */
	NET_INC_STATS(sock_net(sk), LINUX_MIB_RCVPRUNED);

	/* Massive buffer overcommit. */
	tp->pred_flags = 0;
	return -1;
}

static bool tcp_should_expand_sndbuf(const struct sock *sk)
{
	const struct tcp_sock *tp = tcp_sk(sk);

	/* If the user specified a specific send buffer setting, do
	 * not modify it.
	 */
	if (sk->sk_userlocks & SOCK_SNDBUF_LOCK)
		return false;

	/* If we are under global TCP memory pressure, do not expand.  */
	if (tcp_under_memory_pressure(sk))
		return false;

	/* If we are under soft global TCP memory pressure, do not expand.  */
	if (sk_memory_allocated(sk) >= sk_prot_mem_limits(sk, 0))
		return false;

	/* If we filled the congestion window, do not expand.  */
	if (tcp_packets_in_flight(tp) >= tp->snd_cwnd)
		return false;

	return true;
}

/* When incoming ACK allowed to free some skb from write_queue,
 * we remember this event in flag SOCK_QUEUE_SHRUNK and wake up socket
 * on the exit from tcp input handler.
 *
 * PROBLEM: sndbuf expansion does not work well with largesend.
 */
static void tcp_new_space(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);

	if (tcp_should_expand_sndbuf(sk)) { // 应该扩展发送缓存空间
		tcp_sndbuf_expand(sk);
		tp->snd_cwnd_stamp = tcp_jiffies32;
	}

	sk->sk_write_space(sk); // 调用 sock_def_write_space 函数，如果有可用发送空间则通知（唤醒）进程
}

static void tcp_check_space(struct sock *sk)
{
	if (sock_flag(sk, SOCK_QUEUE_SHRUNK)) { // 发送缓存空间曾经收缩过
		sock_reset_flag(sk, SOCK_QUEUE_SHRUNK);
		/* pairs with tcp_poll() */
		smp_mb();
		if (sk->sk_socket &&
		    test_bit(SOCK_NOSPACE, &sk->sk_socket->flags)) {
            // 发生过发送缓存耗尽事件，这意味着可能有进程在等待可用缓存空间
			tcp_new_space(sk);
			if (!test_bit(SOCK_NOSPACE, &sk->sk_socket->flags))
				tcp_chrono_stop(sk, TCP_CHRONO_SNDBUF_LIMITED);
		}
	}
}

static inline void tcp_data_snd_check(struct sock *sk)
{
	tcp_push_pending_frames(sk); // __tcp_push_pending_frames()的包装函数
	tcp_check_space(sk); // 内存管理相关
}

/*
 * Check if sending an ack is needed.
 */
static void __tcp_ack_snd_check(struct sock *sk, int ofo_possible)
{
	struct tcp_sock *tp = tcp_sk(sk);
	unsigned long rtt, delay;

	    /* More than one full frame received... */
	if (((tp->rcv_nxt - tp->rcv_wup) > inet_csk(sk)->icsk_ack.rcv_mss &&
	     /* ... and right edge of window advances far enough.
	      * (tcp_recvmsg() will send ACK otherwise).
	      * If application uses SO_RCVLOWAT, we want send ack now if
	      * we have not received enough bytes to satisfy the condition.
	      */
	    (tp->rcv_nxt - tp->copied_seq < sk->sk_rcvlowat ||
	     __tcp_select_window(sk) >= tp->rcv_wnd)) ||
	    /* We ACK each frame or... */
	    tcp_in_quickack_mode(sk) ||
	    /* Protocol state mandates a one-time immediate ACK */
	    inet_csk(sk)->icsk_ack.pending & ICSK_ACK_NOW) {
send_now:
		tcp_send_ack(sk);
		return;
	}

	if (!ofo_possible || RB_EMPTY_ROOT(&tp->out_of_order_queue)) {
		tcp_send_delayed_ack(sk);
		return;
	}

	if (!tcp_is_sack(tp) ||
	    tp->compressed_ack >= sock_net(sk)->ipv4.sysctl_tcp_comp_sack_nr)
		goto send_now;

	if (tp->compressed_ack_rcv_nxt != tp->rcv_nxt) {
		tp->compressed_ack_rcv_nxt = tp->rcv_nxt;
		tp->dup_ack_counter = 0;
	}
	if (tp->dup_ack_counter < TCP_FASTRETRANS_THRESH) {
		tp->dup_ack_counter++;
		goto send_now;
	}
	tp->compressed_ack++;
	if (hrtimer_is_queued(&tp->compressed_ack_timer))
		return;

	/* compress ack timer : 5 % of rtt, but no more than tcp_comp_sack_delay_ns */

	rtt = tp->rcv_rtt_est.rtt_us;
	if (tp->srtt_us && tp->srtt_us < rtt)
		rtt = tp->srtt_us;

	delay = min_t(unsigned long, sock_net(sk)->ipv4.sysctl_tcp_comp_sack_delay_ns,
		      rtt * (NSEC_PER_USEC >> 3)/20);
	sock_hold(sk);
	hrtimer_start_range_ns(&tp->compressed_ack_timer, ns_to_ktime(delay),
			       sock_net(sk)->ipv4.sysctl_tcp_comp_sack_slack_ns,
			       HRTIMER_MODE_REL_PINNED_SOFT);
}

static inline void tcp_ack_snd_check(struct sock *sk)
{
	if (!inet_csk_ack_scheduled(sk)) {
		/* We sent a data segment already. */
		return;
	}
	__tcp_ack_snd_check(sk, 1);
}

/*
 *	This routine is only called when we have urgent data
 *	signaled. Its the 'slow' part of tcp_urg. It could be
 *	moved inline now as tcp_urg is only called from one
 *	place. We handle URGent data wrong. We have to - as
 *	BSD still doesn't use the correction from RFC961.
 *	For 1003.1g we should support a new option TCP_STDURG to permit
 *	either form (or just set the sysctl tcp_stdurg).
 */

static void tcp_check_urg(struct sock *sk, const struct tcphdr *th)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 ptr = ntohs(th->urg_ptr);

	if (ptr && !sock_net(sk)->ipv4.sysctl_tcp_stdurg)
		ptr--;
	ptr += ntohl(th->seq);

	/* Ignore urgent data that we've already seen and read. */
	if (after(tp->copied_seq, ptr))
		return;

	/* Do not replay urg ptr.
	 *
	 * NOTE: interesting situation not covered by specs.
	 * Misbehaving sender may send urg ptr, pointing to segment,
	 * which we already have in ofo queue. We are not able to fetch
	 * such data and will stay in TCP_URG_NOTYET until will be eaten
	 * by recvmsg(). Seems, we are not obliged to handle such wicked
	 * situations. But it is worth to think about possibility of some
	 * DoSes using some hypothetical application level deadlock.
	 */
	if (before(ptr, tp->rcv_nxt))
		return;

	/* Do we already have a newer (or duplicate) urgent pointer? */
	if (tp->urg_data && !after(ptr, tp->urg_seq))
		return;

	/* Tell the world about our new urgent pointer. */
	sk_send_sigurg(sk);

	/* We may be adding urgent data when the last byte read was
	 * urgent. To do this requires some care. We cannot just ignore
	 * tp->copied_seq since we would read the last urgent byte again
	 * as data, nor can we alter copied_seq until this data arrives
	 * or we break the semantics of SIOCATMARK (and thus sockatmark())
	 *
	 * NOTE. Double Dutch. Rendering to plain English: author of comment
	 * above did something sort of 	send("A", MSG_OOB); send("B", MSG_OOB);
	 * and expect that both A and B disappear from stream. This is _wrong_.
	 * Though this happens in BSD with high probability, this is occasional.
	 * Any application relying on this is buggy. Note also, that fix "works"
	 * only in this artificial test. Insert some normal data between A and B and we will
	 * decline of BSD again. Verdict: it is better to remove to trap
	 * buggy users.
	 */
	if (tp->urg_seq == tp->copied_seq && tp->urg_data &&
	    !sock_flag(sk, SOCK_URGINLINE) && tp->copied_seq != tp->rcv_nxt) {
		struct sk_buff *skb = skb_peek(&sk->sk_receive_queue);
		tp->copied_seq++;
		if (skb && !before(tp->copied_seq, TCP_SKB_CB(skb)->end_seq)) {
			__skb_unlink(skb, &sk->sk_receive_queue);
			__kfree_skb(skb);
		}
	}

	tp->urg_data = TCP_URG_NOTYET;
	WRITE_ONCE(tp->urg_seq, ptr);

	/* Disable header prediction. */
	tp->pred_flags = 0;
}

/* This is the 'fast' part of urgent handling. */
static void tcp_urg(struct sock *sk, struct sk_buff *skb, const struct tcphdr *th)
{
	struct tcp_sock *tp = tcp_sk(sk);

	/* Check if we get a new urgent pointer - normally not. */
	if (th->urg)
		tcp_check_urg(sk, th);

	/* Do we wait for any urgent data? - normally not... */
	if (tp->urg_data == TCP_URG_NOTYET) {
		u32 ptr = tp->urg_seq - ntohl(th->seq) + (th->doff * 4) -
			  th->syn;

		/* Is the urgent pointer pointing into this packet? */
		if (ptr < skb->len) {
			u8 tmp;
			if (skb_copy_bits(skb, ptr, &tmp, 1))
				BUG();
			tp->urg_data = TCP_URG_VALID | tmp;
			if (!sock_flag(sk, SOCK_DEAD))
				sk->sk_data_ready(sk);
		}
	}
}

/* Accept RST for rcv_nxt - 1 after a FIN.
 * When tcp connections are abruptly terminated from Mac OSX (via ^C), a
 * FIN is sent followed by a RST packet. The RST is sent with the same
 * sequence number as the FIN, and thus according to RFC 5961 a challenge
 * ACK should be sent. However, Mac OSX rate limits replies to challenge
 * ACKs on the closed socket. In addition middleboxes can drop either the
 * challenge ACK or a subsequent RST.
 */
static bool tcp_reset_check(const struct sock *sk, const struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);

	return unlikely(TCP_SKB_CB(skb)->seq == (tp->rcv_nxt - 1) &&
			(1 << sk->sk_state) & (TCPF_CLOSE_WAIT | TCPF_LAST_ACK |
					       TCPF_CLOSING));
}

/* Does PAWS and seqno based validation of an incoming segment, flags will
 * play significant role here.
 */
static bool tcp_validate_incoming(struct sock *sk, struct sk_buff *skb,
				  const struct tcphdr *th, int syn_inerr)
{
	struct tcp_sock *tp = tcp_sk(sk);
	bool rst_seq_match = false;

	/* RFC1323: H1. Apply PAWS check first. */
	if (tcp_fast_parse_options(sock_net(sk), skb, th, tp) &&
	    tp->rx_opt.saw_tstamp &&
	    tcp_paws_discard(sk, skb)) {
		if (!th->rst) {
			NET_INC_STATS(sock_net(sk), LINUX_MIB_PAWSESTABREJECTED);
			if (!tcp_oow_rate_limited(sock_net(sk), skb,
						  LINUX_MIB_TCPACKSKIPPEDPAWS,
						  &tp->last_oow_ack_time))
				tcp_send_dupack(sk, skb);
			goto discard;
		}
		/* Reset is accepted even if it did not pass PAWS. */
	}

	/* Step 1: check sequence number */
	// 检查数据包的序号是否正确，该判断失败后调用tcp_send_dupack发送一个duplicate acknowledge（未设置RST标志位时）
	if (!tcp_sequence(tp, TCP_SKB_CB(skb)->seq, TCP_SKB_CB(skb)->end_seq)) {
        // seq 不在窗口内
		/* RFC793, page 37: "In all states except SYN-SENT, all reset
		 * (RST) segments are validated by checking their SEQ-fields."
		 * And page 69: "If an incoming segment is not acceptable,
		 * an acknowledgment should be sent in reply (unless the RST
		 * bit is set, if so drop the segment and return)".
		 */
		if (!th->rst) {
            // RST 标记没有设置
			if (th->syn)
				goto syn_challenge;
			if (!tcp_oow_rate_limited(sock_net(sk), skb,
						  LINUX_MIB_TCPACKSKIPPEDSEQ,
						  &tp->last_oow_ack_time))
				tcp_send_dupack(sk, skb);
		} else if (tcp_reset_check(sk, skb)) {
			tcp_reset(sk);
		}
		goto discard;
	}

	/* Step 2: check RST bit */
	if (th->rst) {
		/* RFC 5961 3.2 (extend to match against (RCV.NXT - 1) after a
		 * FIN and SACK too if available):
		 * If seq num matches RCV.NXT or (RCV.NXT - 1) after a FIN, or
		 * the right-most SACK block,
		 * then
		 *     RESET the connection
		 * else
		 *     Send a challenge ACK
		 */
		if (TCP_SKB_CB(skb)->seq == tp->rcv_nxt ||
		    tcp_reset_check(sk, skb)) {
			rst_seq_match = true;
		} else if (tcp_is_sack(tp) && tp->rx_opt.num_sacks > 0) {
			struct tcp_sack_block *sp = &tp->selective_acks[0];
			int max_sack = sp[0].end_seq;
			int this_sack;

			for (this_sack = 1; this_sack < tp->rx_opt.num_sacks;
			     ++this_sack) {
				max_sack = after(sp[this_sack].end_seq,
						 max_sack) ?
					sp[this_sack].end_seq : max_sack;
			}

			if (TCP_SKB_CB(skb)->seq == max_sack)
				rst_seq_match = true;
		}

		if (rst_seq_match)
			tcp_reset(sk);
		else {
			/* Disable TFO if RST is out-of-order
			 * and no data has been received
			 * for current active TFO socket
			 */
			if (tp->syn_fastopen && !tp->data_segs_in &&
			    sk->sk_state == TCP_ESTABLISHED)
				tcp_fastopen_active_disable(sk);
			tcp_send_challenge_ack(sk, skb);
		}
		goto discard;
	}

	/* step 3: check security and precedence [ignored] */

	/* step 4: Check for a SYN
	 * RFC 5961 4.2 : Send a challenge ack
	 */
	if (th->syn) {
syn_challenge:
        // 处理 SYN Challenge 的情况
		if (syn_inerr)
			TCP_INC_STATS(sock_net(sk), TCP_MIB_INERRS);
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPSYNCHALLENGE);
		tcp_send_challenge_ack(sk, skb);
		goto discard;
	}

	return true;

discard:
	tcp_drop(sk, skb);
	return false;
}

/*
 *	TCP receive function for the ESTABLISHED state.
 *
 *	It is split into a fast path and a slow path. The fast path is
 * 	disabled when:
 *	- A zero window was announced from us - zero window probing
 *        is only handled properly in the slow path.
 *	- Out of order segments arrived.
 *	- Urgent data is expected.
 *	- There is no buffer space left
 *	- Unexpected TCP flags/window values/header lengths are received
 *	  (detected by checking the TCP header against pred_flags)
 *	- Data is sent in both directions. Fast path only supports pure senders
 *	  or pure receivers (this means either the sequence number or the ack
 *	  value must stay constant)
 *	- Unexpected TCP option.
 *
 *	When these conditions are not satisfied it drops into a standard
 *	receive procedure patterned after RFC793 to handle all cases.
 *	The first three cases are guaranteed by proper pred_flags setting,
 *	the rest is checked inline. Fast processing is turned on in
 *	tcp_data_queue when everything is OK.
 */
void tcp_rcv_established(struct sock *sk, struct sk_buff *skb)
{
	const struct tcphdr *th = (const struct tcphdr *)skb->data;
	struct tcp_sock *tp = tcp_sk(sk);
	unsigned int len = skb->len;

	/* TCP congestion window tracking */
	trace_tcp_probe(sk, skb);

	tcp_mstamp_refresh(tp);
    /* 路由为空，则重新设置路由 */
	if (unlikely(!sk->sk_rx_dst))
		inet_csk(sk)->icsk_af_ops->sk_rx_dst_set(sk, skb);
	/*
	 *	Header prediction.
	 *	The code loosely follows the one in the famous
	 *	"30 instruction TCP receive" Van Jacobson mail.
	 *
	 *	Van's trick is to deposit buffers into socket queue
	 *	on a device interrupt, to call tcp_recv function
	 *	on the receive process context and checksum and copy
	 *	the buffer to user space. smart...
	 *
	 *	Our current scheme is not silly either but we take the
	 *	extra cost of the net_bh soft interrupt processing...
	 *	We do checksum and copy also but from device to kernel.
	 */

	tp->rx_opt.saw_tstamp = 0;

	/*	pred_flags is 0xS?10 << 16 + snd_wnd
	 *	if header_prediction is to be made
	 *	'S' will always be tp->tcp_header_len >> 2
	 *	'?' will be 0 for the fast path, otherwise pred_flags is 0 to
	 *  turn it off	(when there are holes in the receive
	 *	 space for instance)
	 *	PSH flag is ignored.
	 */

    /* 快路检查 && 序号正确 && ack序号正确 */
    /* TCP_HP_BITS的作用就是排除flag中的PSH标志位。
     * 只有在头部预测满足并且数据包以正确的顺序（该数据包的第一个序号就是下个要接收的序号）到达时才进入fast path。
     */
	if ((tcp_flag_word(th) & TCP_HP_BITS) == tp->pred_flags &&
	    TCP_SKB_CB(skb)->seq == tp->rcv_nxt &&
	    !after(TCP_SKB_CB(skb)->ack_seq, tp->snd_nxt)) {
        /* tcp头部长度 */
        int tcp_header_len = tp->tcp_header_len;

        /* Timestamp header prediction: tcp_header_len
         * is automatically equal to th->doff*4 due to pred_flags
         * match.
         */

        /* Check timestamp */
        //相等说明tcp timestamp option被打开。
        if (tcp_header_len == sizeof(struct tcphdr) + TCPOLEN_TSTAMP_ALIGNED) {
			/* No? Slow path! */
            //这里主要是 parse timestamp 选项，如果返回 0 则表明 parse 出错，此时我们进入 slow_path
			if (!tcp_parse_aligned_timestamp(tp, th))
                /* 解析时间戳选项失败，执行慢路 */
				goto slow_path;

			/* If PAWS failed, check it more carefully in slow path */
            // 该代码段是依据时戳选项来检查 PAWS（Protect Against Wrapped Sequence numbers）
            /* 序号回转，执行慢路 */
            // 如果上面 parse 成功，则 tp 对应的 rx_opt 域已经被正确赋值，
            // 此时如果 rcv_tsval（新的接收的数据段的时间戳)比 ts_recent(对端发送过来的数据(也就是上一次)的最新的一个时间戳)小，
            // 则我们要进入 slow path 处理 paws
			if ((s32)(tp->rx_opt.rcv_tsval - tp->rx_opt.ts_recent) < 0)
				goto slow_path;

			/* DO NOT update ts_recent here, if checksum fails
			 * and timestamp was corrupted part, it will result
			 * in a hung connection since we will drop all
			 * future packets due to the PAWS test.
			 */
		}

        /* 无数据 */
		if (len <= tcp_header_len) {
			/* Bulk data transfer: sender */
			if (len == tcp_header_len) {
			    /*
			     * 1 保存对方的最近时戳 tcp_store_ts_recent。
			     * 通过前面的if判断可以看出tcp总是回显2次时戳回显直接最先到达的数据包的时戳，
			     * rcv_wup 只在发送数据（这时回显时戳）时重置为 rcv_nxt，
			     * 所以接收到前一次回显后第一个数据包后，rcv_nxt 增加了，但是 rcv_wup 没有更新，
			     * 所以后面的数据包处理时不会调用该函数来保存时戳。
			     * 2 ACK 处理。这个函数非常复杂，包含了拥塞控制机制，确认处理等等。
			     * 3 检查是否有数据待发送 tcp_data_snd_check。
			     */
				/* Predicted packet is in window by definition.
				 * seq == rcv_nxt and rcv_wup <= rcv_nxt.
				 * Hence, check seq<=rcv_wup reduces to:
				 */
                /*
                 * 有时间戳选项 && 所有接收的数据段均确认完毕保存时间戳
                 */
				if (tcp_header_len ==
				    (sizeof(struct tcphdr) + TCPOLEN_TSTAMP_ALIGNED) &&
				    tp->rcv_nxt == tp->rcv_wup)
					tcp_store_ts_recent(tp);

				/* We know that such packets are checksummed
				 * on entry.
				 */
                /* 输入ack处理 */
				tcp_ack(sk, skb, 0);
                /* 释放skb */
				__kfree_skb(skb);
                /* 检查是否有数据要发送，并检查发送缓冲区大小 */
				tcp_data_snd_check(sk);
				/* When receiving pure ack in fast path, update
				 * last ts ecr directly instead of calling
				 * tcp_rcv_rtt_measure_ts()
				 */
				tp->rcv_rtt_last_tsecr = tp->rx_opt.rcv_tsecr;
				return;
			} else { /* Header too small *//* 数据多小，比头部都小，错包 */
				TCP_INC_STATS(sock_net(sk), TCP_MIB_INERRS);
				goto discard;
			}
		} else { /* 有数据 */
			int eaten = 0;
			bool fragstolen = false;

            /* 检查校验和 */
			if (tcp_checksum_complete(skb))
				goto csum_error;

            /* skb长度> 预分配长度 */
			if ((int)skb->truesize > sk->sk_forward_alloc)
				goto step5;

			/* Predicted packet is in window by definition.
			 * seq == rcv_nxt and rcv_wup <= rcv_nxt.
			 * Hence, check seq<=rcv_wup reduces to:
			 */
            /* 有时间戳选项 && 收到的数据段均已确认，更新时间戳 */
			if (tcp_header_len ==
			    (sizeof(struct tcphdr) + TCPOLEN_TSTAMP_ALIGNED) &&
			    tp->rcv_nxt == tp->rcv_wup)
				tcp_store_ts_recent(tp);

            /* 接收端RTT估算 */
			tcp_rcv_rtt_measure_ts(sk, skb);

			NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPHPHITS);

			/* Bulk data transfer: receiver */
			__skb_pull(skb, tcp_header_len);
            /* 数据加入接收队列 */
			eaten = tcp_queue_rcv(sk, skb, &fragstolen); // eaten =0 表示尝试合并失败

            /* 数据包接收后续处理*/
			tcp_event_data_recv(sk, skb);

            /* ACK 处理*/
            /* 确认序号确认了数据 */
			if (TCP_SKB_CB(skb)->ack_seq != tp->snd_una) {
				/* Well, only one small jumplet in fast path... */
                /* 处理ack */
				tcp_ack(sk, skb, FLAG_DATA);
                /* 检查是否有数据要发送，需要则发送 */
				tcp_data_snd_check(sk);
				if (!inet_csk_ack_scheduled(sk))
                    /* 没有ack要发送 */
					goto no_ack;
			}

            /* ACK发送处理 */
            /* 检查是否有ack要发送，需要则发送 */
			__tcp_ack_snd_check(sk, 0);
no_ack:
            /* skb已经合并到前一个段中，则释放之 */
            /* eaten为1，表示数据分段合并成功 */
            if (eaten)
				kfree_skb_partial(skb, fragstolen);
            /* 唤醒用户进程有数据读取 */
			tcp_data_ready(sk);
			return;
		}
	}

slow_path:
    /* 长度错误|| 校验和错误 */
	if (len < (th->doff << 2) || tcp_checksum_complete(skb))
		goto csum_error;

    /* 无ack，无rst，无syn */
	if (!th->ack && !th->rst && !th->syn)
		goto discard;

	/*
	 *	Standard slow path.
	 */

    /* 种种校验 */
	if (!tcp_validate_incoming(sk, skb, th, 1))
		return;

step5:
    /* 处理ack */
	if (tcp_ack(sk, skb, FLAG_SLOWPATH | FLAG_UPDATE_TS_RECENT) < 0)
		goto discard;

    /* 计算rtt */
	tcp_rcv_rtt_measure_ts(sk, skb);

	/* Process urgent data. */
    /* 处理紧急数据 */
	tcp_urg(sk, skb, th);

	/* step 7: process the segment text */
    /* 数据段处理 */
	tcp_data_queue(sk, skb);

    /* 发送数据检查，有则发送 */
	tcp_data_snd_check(sk);
    /* 发送ack检查，有则发送 */
	tcp_ack_snd_check(sk);
	return;

csum_error:
	TCP_INC_STATS(sock_net(sk), TCP_MIB_CSUMERRORS);
	TCP_INC_STATS(sock_net(sk), TCP_MIB_INERRS);

discard:
	tcp_drop(sk, skb);
}
EXPORT_SYMBOL(tcp_rcv_established);

void tcp_init_transfer(struct sock *sk, int bpf_op)
{
	struct inet_connection_sock *icsk = inet_csk(sk);
	struct tcp_sock *tp = tcp_sk(sk);

	tcp_mtup_init(sk);
	icsk->icsk_af_ops->rebuild_header(sk);
	tcp_init_metrics(sk);

	/* Initialize the congestion window to start the transfer.
	 * Cut cwnd down to 1 per RFC5681 if SYN or SYN-ACK has been
	 * retransmitted. In light of RFC6298 more aggressive 1sec
	 * initRTO, we only reset cwnd when more than 1 SYN/SYN-ACK
	 * retransmission has occurred.
	 */
	if (tp->total_retrans > 1 && tp->undo_marker)
		tp->snd_cwnd = 1;
	else
		tp->snd_cwnd = tcp_init_cwnd(tp, __sk_dst_get(sk));
	tp->snd_cwnd_stamp = tcp_jiffies32;

	tcp_call_bpf(sk, bpf_op, 0, NULL);
	tcp_init_congestion_control(sk);
	tcp_init_buffer_space(sk);
}

void tcp_finish_connect(struct sock *sk, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct inet_connection_sock *icsk = inet_csk(sk);

	tcp_set_state(sk, TCP_ESTABLISHED);
	icsk->icsk_ack.lrcvtime = tcp_jiffies32;

	if (skb) {
		icsk->icsk_af_ops->sk_rx_dst_set(sk, skb);
		security_inet_conn_established(sk, skb);
		sk_mark_napi_id(sk, skb);
	}

	tcp_init_transfer(sk, BPF_SOCK_OPS_ACTIVE_ESTABLISHED_CB);

	/* Prevent spurious tcp_cwnd_restart() on first data
	 * packet.
	 */
	tp->lsndtime = tcp_jiffies32;

	if (sock_flag(sk, SOCK_KEEPOPEN))
		inet_csk_reset_keepalive_timer(sk, keepalive_time_when(tp));

	if (!tp->rx_opt.snd_wscale)
		__tcp_fast_path_on(tp, tp->snd_wnd);
	else
		tp->pred_flags = 0;
}

static bool tcp_rcv_fastopen_synack(struct sock *sk, struct sk_buff *synack,
				    struct tcp_fastopen_cookie *cookie)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct sk_buff *data = tp->syn_data ? tcp_rtx_queue_head(sk) : NULL;
	u16 mss = tp->rx_opt.mss_clamp, try_exp = 0;
	bool syn_drop = false;

	if (mss == tp->rx_opt.user_mss) {
		struct tcp_options_received opt;

		/* Get original SYNACK MSS value if user MSS sets mss_clamp */
		tcp_clear_options(&opt);
		opt.user_mss = opt.mss_clamp = 0;
		tcp_parse_options(sock_net(sk), synack, &opt, 0, NULL);
		mss = opt.mss_clamp;
	}

	if (!tp->syn_fastopen) {
		/* Ignore an unsolicited cookie */
		cookie->len = -1;
	} else if (tp->total_retrans) {
		/* SYN timed out and the SYN-ACK neither has a cookie nor
		 * acknowledges data. Presumably the remote received only
		 * the retransmitted (regular) SYNs: either the original
		 * SYN-data or the corresponding SYN-ACK was dropped.
		 */
		syn_drop = (cookie->len < 0 && data);
	} else if (cookie->len < 0 && !tp->syn_data) {
		/* We requested a cookie but didn't get it. If we did not use
		 * the (old) exp opt format then try so next time (try_exp=1).
		 * Otherwise we go back to use the RFC7413 opt (try_exp=2).
		 */
		try_exp = tp->syn_fastopen_exp ? 2 : 1;
	}

	tcp_fastopen_cache_set(sk, mss, cookie, syn_drop, try_exp);

	if (data) { /* Retransmit unacked data in SYN */
		if (tp->total_retrans)
			tp->fastopen_client_fail = TFO_SYN_RETRANSMITTED;
		else
			tp->fastopen_client_fail = TFO_DATA_NOT_ACKED;
		skb_rbtree_walk_from(data) {
			if (__tcp_retransmit_skb(sk, data, 1))
				break;
		}
		tcp_rearm_rto(sk);
		NET_INC_STATS(sock_net(sk),
				LINUX_MIB_TCPFASTOPENACTIVEFAIL);
		return true;
	}
	tp->syn_data_acked = tp->syn_data;
	if (tp->syn_data_acked) {
		NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPFASTOPENACTIVE);
		/* SYN-data is counted as two separate packets in tcp_ack() */
		if (tp->delivered > 1)
			--tp->delivered;
	}

	tcp_fastopen_add_skb(sk, synack);

	return false;
}

static void smc_check_reset_syn(struct tcp_sock *tp)
{
#if IS_ENABLED(CONFIG_SMC)
	if (static_branch_unlikely(&tcp_have_smc)) {
		if (tp->syn_smc && !tp->rx_opt.smc_ok)
			tp->syn_smc = 0;
	}
#endif
}

static void tcp_try_undo_spurious_syn(struct sock *sk)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u32 syn_stamp;

	/* undo_marker is set when SYN or SYNACK times out. The timeout is
	 * spurious if the ACK's timestamp option echo value matches the
	 * original SYN timestamp.
	 */
	syn_stamp = tp->retrans_stamp;
	if (tp->undo_marker && syn_stamp && tp->rx_opt.saw_tstamp &&
	    syn_stamp == tp->rx_opt.rcv_tsecr)
		tp->undo_marker = 0;
}

static int tcp_rcv_synsent_state_process(struct sock *sk, struct sk_buff *skb,
					 const struct tcphdr *th)
{
	struct inet_connection_sock *icsk = inet_csk(sk);
	struct tcp_sock *tp = tcp_sk(sk);
	struct tcp_fastopen_cookie foc = { .len = -1 };
	int saved_clamp = tp->rx_opt.mss_clamp;
	bool fastopen_fail;

	tcp_parse_options(sock_net(sk), skb, &tp->rx_opt, 0, &foc);
	if (tp->rx_opt.saw_tstamp && tp->rx_opt.rcv_tsecr)
		tp->rx_opt.rcv_tsecr -= tp->tsoffset;

	if (th->ack) {
		/* rfc793:
		 * "If the state is SYN-SENT then
		 *    first check the ACK bit
		 *      If the ACK bit is set
		 *	  If SEG.ACK =< ISS, or SEG.ACK > SND.NXT, send
		 *        a reset (unless the RST bit is set, if so drop
		 *        the segment and return)"
		 */
		if (!after(TCP_SKB_CB(skb)->ack_seq, tp->snd_una) ||
		    after(TCP_SKB_CB(skb)->ack_seq, tp->snd_nxt)) {
			/* Previous FIN/ACK or RST/ACK might be ignored. */
			if (icsk->icsk_retransmits == 0)
				inet_csk_reset_xmit_timer(sk,
						ICSK_TIME_RETRANS,
						TCP_TIMEOUT_MIN, TCP_RTO_MAX);
			goto reset_and_undo;
		}

		if (tp->rx_opt.saw_tstamp && tp->rx_opt.rcv_tsecr &&
		    !between(tp->rx_opt.rcv_tsecr, tp->retrans_stamp,
			     tcp_time_stamp(tp))) {
			NET_INC_STATS(sock_net(sk),
					LINUX_MIB_PAWSACTIVEREJECTED);
			goto reset_and_undo;
		}

		/* Now ACK is acceptable.
		 *
		 * "If the RST bit is set
		 *    If the ACK was acceptable then signal the user "error:
		 *    connection reset", drop the segment, enter CLOSED state,
		 *    delete TCB, and return."
		 */

		if (th->rst) {
			tcp_reset(sk);
			goto discard;
		}

		/* rfc793:
		 *   "fifth, if neither of the SYN or RST bits is set then
		 *    drop the segment and return."
		 *
		 *    See note below!
		 *                                        --ANK(990513)
		 */
		if (!th->syn)
			goto discard_and_undo;

		/* rfc793:
		 *   "If the SYN bit is on ...
		 *    are acceptable then ...
		 *    (our SYN has been ACKed), change the connection
		 *    state to ESTABLISHED..."
		 */

		tcp_ecn_rcv_synack(tp, th);

		tcp_init_wl(tp, TCP_SKB_CB(skb)->seq);
		tcp_try_undo_spurious_syn(sk);
		tcp_ack(sk, skb, FLAG_SLOWPATH);

		/* Ok.. it's good. Set up sequence numbers and
		 * move to established.
		 */
		WRITE_ONCE(tp->rcv_nxt, TCP_SKB_CB(skb)->seq + 1);
		tp->rcv_wup = TCP_SKB_CB(skb)->seq + 1;

		/* RFC1323: The window in SYN & SYN/ACK segments is
		 * never scaled.
		 */
		tp->snd_wnd = ntohs(th->window);

		if (!tp->rx_opt.wscale_ok) {
			tp->rx_opt.snd_wscale = tp->rx_opt.rcv_wscale = 0;
			tp->window_clamp = min(tp->window_clamp, 65535U);
		}

		if (tp->rx_opt.saw_tstamp) {
			tp->rx_opt.tstamp_ok	   = 1;
			tp->tcp_header_len =
				sizeof(struct tcphdr) + TCPOLEN_TSTAMP_ALIGNED;
			tp->advmss	    -= TCPOLEN_TSTAMP_ALIGNED;
			tcp_store_ts_recent(tp);
		} else {
			tp->tcp_header_len = sizeof(struct tcphdr);
		}

		tcp_sync_mss(sk, icsk->icsk_pmtu_cookie);
		tcp_initialize_rcv_mss(sk);

		/* Remember, tcp_poll() does not lock socket!
		 * Change state from SYN-SENT only after copied_seq
		 * is initialized. */
		WRITE_ONCE(tp->copied_seq, tp->rcv_nxt);

		smc_check_reset_syn(tp);

		smp_mb();

		tcp_finish_connect(sk, skb);

		fastopen_fail = (tp->syn_fastopen || tp->syn_data) &&
				tcp_rcv_fastopen_synack(sk, skb, &foc);

		if (!sock_flag(sk, SOCK_DEAD)) {
			sk->sk_state_change(sk);
			sk_wake_async(sk, SOCK_WAKE_IO, POLL_OUT);
		}
		if (fastopen_fail)
			return -1;
		if (sk->sk_write_pending ||
		    icsk->icsk_accept_queue.rskq_defer_accept ||
		    inet_csk_in_pingpong_mode(sk)) {
			/* Save one ACK. Data will be ready after
			 * several ticks, if write_pending is set.
			 *
			 * It may be deleted, but with this feature tcpdumps
			 * look so _wonderfully_ clever, that I was not able
			 * to stand against the temptation 8)     --ANK
			 */
			inet_csk_schedule_ack(sk);
			tcp_enter_quickack_mode(sk, TCP_MAX_QUICKACKS);
			inet_csk_reset_xmit_timer(sk, ICSK_TIME_DACK,
						  TCP_DELACK_MAX, TCP_RTO_MAX);

discard:
			tcp_drop(sk, skb);
			return 0;
		} else {
			tcp_send_ack(sk);
		}
		return -1;
	}

	/* No ACK in the segment */

	if (th->rst) {
		/* rfc793:
		 * "If the RST bit is set
		 *
		 *      Otherwise (no ACK) drop the segment and return."
		 */

		goto discard_and_undo;
	}

	/* PAWS check. */
	if (tp->rx_opt.ts_recent_stamp && tp->rx_opt.saw_tstamp &&
	    tcp_paws_reject(&tp->rx_opt, 0))
		goto discard_and_undo;

	if (th->syn) {
		/* We see SYN without ACK. It is attempt of
		 * simultaneous connect with crossed SYNs.
		 * Particularly, it can be connect to self.
		 */
		tcp_set_state(sk, TCP_SYN_RECV);

		if (tp->rx_opt.saw_tstamp) {
			tp->rx_opt.tstamp_ok = 1;
			tcp_store_ts_recent(tp);
			tp->tcp_header_len =
				sizeof(struct tcphdr) + TCPOLEN_TSTAMP_ALIGNED;
		} else {
			tp->tcp_header_len = sizeof(struct tcphdr);
		}

		WRITE_ONCE(tp->rcv_nxt, TCP_SKB_CB(skb)->seq + 1);
		WRITE_ONCE(tp->copied_seq, tp->rcv_nxt);
		tp->rcv_wup = TCP_SKB_CB(skb)->seq + 1;

		/* RFC1323: The window in SYN & SYN/ACK segments is
		 * never scaled.
		 */
		tp->snd_wnd    = ntohs(th->window);
		tp->snd_wl1    = TCP_SKB_CB(skb)->seq;
		tp->max_window = tp->snd_wnd;

		tcp_ecn_rcv_syn(tp, th);

		tcp_mtup_init(sk);
		tcp_sync_mss(sk, icsk->icsk_pmtu_cookie);
		tcp_initialize_rcv_mss(sk);

		tcp_send_synack(sk);
#if 0
		/* Note, we could accept data and URG from this segment.
		 * There are no obstacles to make this (except that we must
		 * either change tcp_recvmsg() to prevent it from returning data
		 * before 3WHS completes per RFC793, or employ TCP Fast Open).
		 *
		 * However, if we ignore data in ACKless segments sometimes,
		 * we have no reasons to accept it sometimes.
		 * Also, seems the code doing it in step6 of tcp_rcv_state_process
		 * is not flawless. So, discard packet for sanity.
		 * Uncomment this return to process the data.
		 */
		return -1;
#else
		goto discard;
#endif
	}
	/* "fifth, if neither of the SYN or RST bits is set then
	 * drop the segment and return."
	 */

discard_and_undo:
	tcp_clear_options(&tp->rx_opt);
	tp->rx_opt.mss_clamp = saved_clamp;
	goto discard;

reset_and_undo:
	tcp_clear_options(&tp->rx_opt);
	tp->rx_opt.mss_clamp = saved_clamp;
	return 1;
}

static void tcp_rcv_synrecv_state_fastopen(struct sock *sk)
{
	struct request_sock *req;

	/* If we are still handling the SYNACK RTO, see if timestamp ECR allows
	 * undo. If peer SACKs triggered fast recovery, we can't undo here.
	 */
	if (inet_csk(sk)->icsk_ca_state == TCP_CA_Loss)
		tcp_try_undo_loss(sk, false);

	/* Reset rtx states to prevent spurious retransmits_timed_out() */
	tcp_sk(sk)->retrans_stamp = 0;
	inet_csk(sk)->icsk_retransmits = 0;

	/* Once we leave TCP_SYN_RECV or TCP_FIN_WAIT_1,
	 * we no longer need req so release it.
	 */
	req = rcu_dereference_protected(tcp_sk(sk)->fastopen_rsk,
					lockdep_sock_is_held(sk));
	reqsk_fastopen_remove(sk, req, false);

	/* Re-arm the timer because data may have been sent out.
	 * This is similar to the regular data transmission case
	 * when new data has just been ack'ed.
	 *
	 * (TFO) - we could try to be more aggressive and
	 * retransmitting any data sooner based on when they
	 * are sent out.
	 */
	tcp_rearm_rto(sk);
}

/*
 *	This function implements the receiving procedure of RFC 793 for
 *	all states except ESTABLISHED and TIME_WAIT.
 *	It's called from both tcp_v4_rcv and tcp_v6_rcv and should be
 *	address independent.
 */

int tcp_rcv_state_process(struct sock *sk, struct sk_buff *skb)
{
	struct tcp_sock *tp = tcp_sk(sk);
	struct inet_connection_sock *icsk = inet_csk(sk);
	const struct tcphdr *th = tcp_hdr(skb);
	struct request_sock *req;
	int queued = 0;
	bool acceptable;

	switch (sk->sk_state) {
	case TCP_CLOSE:
		goto discard;

	case TCP_LISTEN:
        //服务器端收到SYN
        /*
         * 在半连接的LISTEN状态下，只处理SYN段。如果是
         * ACK段，此时连接尚未开始建立，因此返回1。在调用
         * tcp_rcv_state_process()函数中会给对方发送RST段；
         * 如果接收的是RST段，则丢弃
         */
		if (th->ack)
			return 1;

		if (th->rst)
			goto discard;

		if (th->syn) {
			if (th->fin)
				goto discard;
			/* It is possible that we process SYN packets from backlog,
			 * so we need to make sure to disable BH and RCU right there.
			 */
            /*
             * 处理SYN段，主要由conn_request接口(TCP中为tcp_v4_conn_request)处理，
             * icsk_af_ops成员在创建套接字时被初始化，参见tcp_v4_init_sock()
             */
            /*
             * 收到三次握手的第一步SYN，
             * 则在tcp_v4_conn_request中创建连接请求控制块request_sock
             */
			rcu_read_lock();
			local_bh_disable();
			acceptable = icsk->icsk_af_ops->conn_request(sk, skb) >= 0; // ipv4_specific--->tcp_v4_conn_request
			local_bh_enable();
			rcu_read_unlock();

			if (!acceptable)
				return 1;
			consume_skb(skb); // free an skbuff
			return 0;
		}
		goto discard;

	case TCP_SYN_SENT:
        //客户端收到SYN+ACK

        /*
         * 对于TCP_SYN_SENT状态的sock，会调用tcp_rcv_synsent_state_process来进行处理
         * 解析tcp选项，获取服务端的支持情况， 比如sack, TFO, wscale, MSS， timestamp等
         * 如果有ack， 进行tcp_ack， 这时候可能fastopen确认了之前的数据
         * 调用tcp_finish_connect，TCP_SYN_SENT->TCP_ESTABLISHED
         * 如果包含fastopen cookie则保存
         * 判断是否需要立即ack还是延时ack
         * 如果包里没有ack，只有syn，则表示相互connect， TCP_SYN_SENT->TCP_SYN_RECV, 并发送synack
         */
		tp->rx_opt.saw_tstamp = 0;
		tcp_mstamp_refresh(tp);
		queued = tcp_rcv_synsent_state_process(sk, skb, th);
		if (queued >= 0)
			return queued;

		/* Do step6 onward by hand. */
		tcp_urg(sk, skb, th);
		__kfree_skb(skb);
		tcp_data_snd_check(sk);
		return 0;
	}

	tcp_mstamp_refresh(tp);
	tp->rx_opt.saw_tstamp = 0;
	req = rcu_dereference_protected(tp->fastopen_rsk,
					lockdep_sock_is_held(sk));
	if (req) {
		bool req_stolen;

		WARN_ON_ONCE(sk->sk_state != TCP_SYN_RECV &&
		    sk->sk_state != TCP_FIN_WAIT1);

		if (!tcp_check_req(sk, skb, req, true, &req_stolen))
			goto discard;
	}

	if (!th->ack && !th->rst && !th->syn)
		goto discard;

	if (!tcp_validate_incoming(sk, skb, th, 0))
		return 0;

    /*
     * 处理TCP段ACK标志，tcp_ack()返回非零值表示处理ACK段成功，是正常的第三次握手TCP段
     */
	/* step 5: check the ACK field */
	acceptable = tcp_ack(sk, skb, FLAG_SLOWPATH |
				      FLAG_UPDATE_TS_RECENT |
				      FLAG_NO_CHALLENGE_ACK) > 0;

    /*
     * tcp_rcv_state_process函数中对于ack的处理步骤中，假如连接处于FIN_WAIT_1，
     * 且数据均已经被确认完，则进入TIME_WAIT_2状态；如果无需在该状态等待（linger2<0），
     * 或者收到了乱序数据段，则直接关闭连接；如果需要等待，
     * 则需要判断等待时间与TIMEWAIT时间的大小关系，若>TIMEWAIT_LEN，
     * 则添加TIME_WAIT_2定时器，否则直接进入TIME_WAIT接管(其子状态仍然是FIN_WAIT_2)，
     * 接管之后会添加TIME_WAIT定时器；
     */
	if (!acceptable) {
		if (sk->sk_state == TCP_SYN_RECV)
			return 1;	/* send one RST */
		tcp_send_challenge_ack(sk, skb);
		goto discard;
	}
	switch (sk->sk_state) {
	case TCP_SYN_RECV:
		tp->delivered++; /* SYN-ACK delivery isn't tracked in tcp_ack */
		if (!tp->srtt_us)
			tcp_synack_rtt_meas(sk, req);

		/* 这里是由tcp_v4_do_rcv里面的tcp_child_process走到这里，
		 * 在tcp_child_process前会通过tcp_check_req创建一个新的struct sock
		 * Once we leave TCP_SYN_RECV, we no longer need req
		 * so release it.
		 */
		if (req) {
			tcp_rcv_synrecv_state_fastopen(sk);
		} else {
			tcp_try_undo_spurious_syn(sk);
			tp->retrans_stamp = 0;
			tcp_init_transfer(sk, BPF_SOCK_OPS_PASSIVE_ESTABLISHED_CB);
			WRITE_ONCE(tp->copied_seq, tp->rcv_nxt);
		}
		smp_mb();
		tcp_set_state(sk, TCP_ESTABLISHED); // TCP_SYN_RECV->TCP_ESTABLISHED
		sk->sk_state_change(sk); // sock_def_wakeup, 唤醒epoll
		/*
            sock_init_data中有
            sk->sk_state_change    =    sock_def_wakeup;
		    sk->sk_data_ready      =    sock_def_readable;
            sk->sk_write_space     =    sock_def_write_space;
            sk->sk_error_report    =    sock_def_error_report;
            sk->sk_destruct        =    sock_def_destruct;
        */
        // epoll然后调用ep_send_events->ep_scan_ready_list->ep_send_events_proc->ep_item_poll->tcp_poll
        /*
         * 设置"子"传输控制块为ESTABLISHED状态
         */

		/* Note, that this wakeup is only for marginal crossed SYN case.
		 * Passively open sockets are not waked up, because
		 * sk->sk_sleep == NULL and sk->sk_socket == NULL.
		 */
		if (sk->sk_socket)
			sk_wake_async(sk, SOCK_WAKE_IO, POLL_OUT);

		/*
         * 初始化传输控制块各字段，如果存在时间戳选项，
         * 同时平滑RTT为零，则需计算重传超时时间等
         */
		tp->snd_una = TCP_SKB_CB(skb)->ack_seq;
		tp->snd_wnd = ntohs(th->window) << tp->rx_opt.snd_wscale;
		tcp_init_wl(tp, TCP_SKB_CB(skb)->seq);

		if (tp->rx_opt.tstamp_ok)
			tp->advmss -= TCPOLEN_TSTAMP_ALIGNED;

		if (!inet_csk(sk)->icsk_ca_ops->cong_control)
            /*
             * 为该套接字建立路由，初始化拥塞控制模块
             */
            /*
             * 初始化与路径MTU有关的成员
             */
			tcp_update_pacing_rate(sk);

		/*
		 * 更新最近一次发送数据包的时间
		 */
		/* Prevent spurious tcp_cwnd_restart() on first data packet */
		tp->lsndtime = tcp_jiffies32;

		tcp_initialize_rcv_mss(sk);
		/*
		 * 计算有关TCP首部预测的标志
		 */
		tcp_fast_path_on(tp);
		break;

	case TCP_FIN_WAIT1: {
		int tmo;

		if (req)
			tcp_rcv_synrecv_state_fastopen(sk);

        /* 发送数据未确认完毕 */
		if (tp->snd_una != tp->write_seq)
			break;

		tcp_set_state(sk, TCP_FIN_WAIT2); /* 进入FIN_WAIT_2状态 */
		sk->sk_shutdown |= SEND_SHUTDOWN; /* 关闭发送端 */

		sk_dst_confirm(sk); /* 路由缓存确认 */

		if (!sock_flag(sk, SOCK_DEAD)) {
			/* Wake up lingering close() */
			sk->sk_state_change(sk); /* 套接口不是DEAD状态，状态发生变化，唤醒等待进程 */
			break;
		}

        /* linger2<0，无需在FIN_WAIT_2等待 */
		if (tp->linger2 < 0) {
            /* 关闭连接 */
			tcp_done(sk);
			NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPABORTONDATA);
			return 1;
		}
        /* 收到期望序号以后的数据段(data, fin) */
		if (TCP_SKB_CB(skb)->end_seq != TCP_SKB_CB(skb)->seq &&
		    after(TCP_SKB_CB(skb)->end_seq - th->fin, tp->rcv_nxt)) {
			/* Receive out of order FIN after close() */
			if (tp->syn_fastopen && th->fin)
				tcp_fastopen_active_disable(sk);
			tcp_done(sk);
			NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPABORTONDATA);
			return 1;
		}

        /* 获取FIN_WAIT_2等待时间 */
		tmo = tcp_fin_time(sk);
        /* > TIMEWAIT_LEN，加入FIN_WAIT_2定时器 */
		if (tmo > TCP_TIMEWAIT_LEN) {
			inet_csk_reset_keepalive_timer(sk, tmo - TCP_TIMEWAIT_LEN);
		} else if (th->fin || sock_owned_by_user(sk)) {
			/* Bad case. We could lose such FIN otherwise.
			 * It is not a big problem, but it looks confusing
			 * and not so rare event. We still can lose it now,
			 * if it spins in bh_lock_sock(), but it is really
			 * marginal case.
			 */
            /* 有fin?? 或者 被用户进程锁定，加入FIN_WAIT_2定时器 */
			inet_csk_reset_keepalive_timer(sk, tmo);
		} else {
            /* 正常等待时间< TIMEWAIT_LEN，进入TIMEWAIT接管状态 */
			tcp_time_wait(sk, TCP_FIN_WAIT2, tmo);
			goto discard;
		}
		break;
	}

	case TCP_CLOSING:
		if (tp->snd_una == tp->write_seq) {
			tcp_time_wait(sk, TCP_TIME_WAIT, 0);
			goto discard;
		}
		break;

	case TCP_LAST_ACK:
		if (tp->snd_una == tp->write_seq) {
			tcp_update_metrics(sk);
			tcp_done(sk);
			goto discard;
		}
		break;
	}

	/* step 6: check the URG bit */
	tcp_urg(sk, skb, th);

    /*
     * FIN_WAIT_2状态的走向有以下几个流程触发点，
     * (1)TIME_WAIT_2定时器未超时时间内，收到数据段触发；
     * (2)TIME_WAIT_2定时器超时触发；
     * (3)TIME_WAIT定时器未超时时间内，收到数据段触发；
     * (4)TIME_WAIT定时器超时触发；
*/
	/* step 7: process the segment text */
	switch (sk->sk_state) {
	case TCP_CLOSE_WAIT:
	case TCP_CLOSING:
	case TCP_LAST_ACK:
		if (!before(TCP_SKB_CB(skb)->seq, tp->rcv_nxt)) {
			if (sk_is_mptcp(sk))
				mptcp_incoming_options(sk, skb, &tp->rx_opt);
			break;
		}
		fallthrough;
	case TCP_FIN_WAIT1:
	case TCP_FIN_WAIT2:
		/* RFC 793 says to queue data in these states,
		 * RFC 1122 says we MUST send a reset.
		 * BSD 4.4 also does reset.
		 */
        //TIME_WAIT_2定时器未超时时间内，收到数据段触发，如果设置FIN标记，则直接进入TIME_WAIT状态；
		if (sk->sk_shutdown & RCV_SHUTDOWN) {
			if (TCP_SKB_CB(skb)->end_seq != TCP_SKB_CB(skb)->seq &&
			    after(TCP_SKB_CB(skb)->end_seq - th->fin, tp->rcv_nxt)) {
				NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPABORTONDATA);
				tcp_reset(sk);
				return 1;
			}
		}
		fallthrough;
	case TCP_ESTABLISHED:
		tcp_data_queue(sk, skb);
		queued = 1;
		break;
	}

	/* tcp_data could move socket to TIME-WAIT */
	if (sk->sk_state != TCP_CLOSE) {
		tcp_data_snd_check(sk);
		tcp_ack_snd_check(sk);
	}

	if (!queued) {
discard:
		tcp_drop(sk, skb);
	}
	return 0;
}
EXPORT_SYMBOL(tcp_rcv_state_process);

static inline void pr_drop_req(struct request_sock *req, __u16 port, int family)
{
	struct inet_request_sock *ireq = inet_rsk(req);

	if (family == AF_INET)
		net_dbg_ratelimited("drop open request from %pI4/%u\n",
				    &ireq->ir_rmt_addr, port);
#if IS_ENABLED(CONFIG_IPV6)
	else if (family == AF_INET6)
		net_dbg_ratelimited("drop open request from %pI6/%u\n",
				    &ireq->ir_v6_rmt_addr, port);
#endif
}

/* RFC3168 : 6.1.1 SYN packets must not have ECT/ECN bits set
 *
 * If we receive a SYN packet with these bits set, it means a
 * network is playing bad games with TOS bits. In order to
 * avoid possible false congestion notifications, we disable
 * TCP ECN negotiation.
 *
 * Exception: tcp_ca wants ECN. This is required for DCTCP
 * congestion control: Linux DCTCP asserts ECT on all packets,
 * including SYN, which is most optimal solution; however,
 * others, such as FreeBSD do not.
 *
 * Exception: At least one of the reserved bits of the TCP header (th->res1) is
 * set, indicating the use of a future TCP extension (such as AccECN). See
 * RFC8311 §4.3 which updates RFC3168 to allow the development of such
 * extensions.
 */
static void tcp_ecn_create_request(struct request_sock *req,
				   const struct sk_buff *skb,
				   const struct sock *listen_sk,
				   const struct dst_entry *dst)
{
	const struct tcphdr *th = tcp_hdr(skb);
	const struct net *net = sock_net(listen_sk);
	bool th_ecn = th->ece && th->cwr;
	bool ect, ecn_ok;
	u32 ecn_ok_dst;

	if (!th_ecn)
		return;

	ect = !INET_ECN_is_not_ect(TCP_SKB_CB(skb)->ip_dsfield);
	ecn_ok_dst = dst_feature(dst, DST_FEATURE_ECN_MASK);
	ecn_ok = net->ipv4.sysctl_tcp_ecn || ecn_ok_dst;

	if (((!ect || th->res1) && ecn_ok) || tcp_ca_needs_ecn(listen_sk) ||
	    (ecn_ok_dst & DST_FEATURE_ECN_CA) ||
	    tcp_bpf_ca_needs_ecn((struct sock *)req))
		inet_rsk(req)->ecn_ok = 1;
}

static void tcp_openreq_init(struct request_sock *req,
			     const struct tcp_options_received *rx_opt,
			     struct sk_buff *skb, const struct sock *sk)
{
	struct inet_request_sock *ireq = inet_rsk(req);

	req->rsk_rcv_wnd = 0;		/* So that tcp_send_synack() knows! */
	req->cookie_ts = 0;
	tcp_rsk(req)->rcv_isn = TCP_SKB_CB(skb)->seq;
	tcp_rsk(req)->rcv_nxt = TCP_SKB_CB(skb)->seq + 1;
	tcp_rsk(req)->snt_synack = 0;
	tcp_rsk(req)->last_oow_ack_time = 0;
	req->mss = rx_opt->mss_clamp;
	req->ts_recent = rx_opt->saw_tstamp ? rx_opt->rcv_tsval : 0;
	ireq->tstamp_ok = rx_opt->tstamp_ok;
	ireq->sack_ok = rx_opt->sack_ok;
	ireq->snd_wscale = rx_opt->snd_wscale;
	ireq->wscale_ok = rx_opt->wscale_ok;
	ireq->acked = 0;
	ireq->ecn_ok = 0;
	ireq->ir_rmt_port = tcp_hdr(skb)->source;
	ireq->ir_num = ntohs(tcp_hdr(skb)->dest);
	ireq->ir_mark = inet_request_mark(sk, skb);
#if IS_ENABLED(CONFIG_SMC)
	ireq->smc_ok = rx_opt->smc_ok;
#endif
}

struct request_sock *inet_reqsk_alloc(const struct request_sock_ops *ops,
				      struct sock *sk_listener,
				      bool attach_listener)
{
	struct request_sock *req = reqsk_alloc(ops, sk_listener,
					       attach_listener);

	if (req) {
		struct inet_request_sock *ireq = inet_rsk(req);

		ireq->ireq_opt = NULL;
#if IS_ENABLED(CONFIG_IPV6)
		ireq->pktopts = NULL;
#endif
		atomic64_set(&ireq->ir_cookie, 0);
		ireq->ireq_state = TCP_NEW_SYN_RECV;
		write_pnet(&ireq->ireq_net, sock_net(sk_listener));
		ireq->ireq_family = sk_listener->sk_family;
	}

	return req;
}
EXPORT_SYMBOL(inet_reqsk_alloc);

/*
 * Return true if a syncookie should be sent
 */
static bool tcp_syn_flood_action(const struct sock *sk, const char *proto)
{
	struct request_sock_queue *queue = &inet_csk(sk)->icsk_accept_queue;
	const char *msg = "Dropping request";
	bool want_cookie = false;
	struct net *net = sock_net(sk);

#ifdef CONFIG_SYN_COOKIES
	if (net->ipv4.sysctl_tcp_syncookies) {
		msg = "Sending cookies";
		want_cookie = true;
		__NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPREQQFULLDOCOOKIES);
	} else
#endif
		__NET_INC_STATS(sock_net(sk), LINUX_MIB_TCPREQQFULLDROP);

	if (!queue->synflood_warned &&
	    net->ipv4.sysctl_tcp_syncookies != 2 &&
	    xchg(&queue->synflood_warned, 1) == 0)
		net_info_ratelimited("%s: Possible SYN flooding on port %d. %s.  Check SNMP counters.\n",
				     proto, sk->sk_num, msg);

	return want_cookie;
}

static void tcp_reqsk_record_syn(const struct sock *sk,
				 struct request_sock *req,
				 const struct sk_buff *skb)
{
	if (tcp_sk(sk)->save_syn) {
		u32 len = skb_network_header_len(skb) + tcp_hdrlen(skb);
		u32 *copy;

		copy = kmalloc(len + sizeof(u32), GFP_ATOMIC);
		if (copy) {
			copy[0] = len;
			memcpy(&copy[1], skb_network_header(skb), len);
			req->saved_syn = copy;
		}
	}
}

/* If a SYN cookie is required and supported, returns a clamped MSS value to be
 * used for SYN cookie generation.
 */
u16 tcp_get_syncookie_mss(struct request_sock_ops *rsk_ops,
			  const struct tcp_request_sock_ops *af_ops,
			  struct sock *sk, struct tcphdr *th)
{
	struct tcp_sock *tp = tcp_sk(sk);
	u16 mss;

	if (sock_net(sk)->ipv4.sysctl_tcp_syncookies != 2 &&
	    !inet_csk_reqsk_queue_is_full(sk))
		return 0;

	if (!tcp_syn_flood_action(sk, rsk_ops->slab_name))
		return 0;

	if (sk_acceptq_is_full(sk)) {
		NET_INC_STATS(sock_net(sk), LINUX_MIB_LISTENOVERFLOWS);
		return 0;
	}

	mss = tcp_parse_mss_option(th, tp->rx_opt.user_mss);
	if (!mss)
		mss = af_ops->mss_clamp;

	return mss;
}
EXPORT_SYMBOL_GPL(tcp_get_syncookie_mss);

/*
 * 服务器端收到SYN后，创建连接控制块request_sock
 * 也就是收到第一步SYN的时候只是建立的连接控制块request_sock
 * 当收到第三次ack的时候，才创建新的struct sock
 */
int tcp_conn_request(struct request_sock_ops *rsk_ops,
		     const struct tcp_request_sock_ops *af_ops,
		     struct sock *sk, struct sk_buff *skb)
{
	struct tcp_fastopen_cookie foc = { .len = -1 };
	__u32 isn = TCP_SKB_CB(skb)->tcp_tw_isn;
	struct tcp_options_received tmp_opt;
	struct tcp_sock *tp = tcp_sk(sk);
	struct net *net = sock_net(sk);
	struct sock *fastopen_sk = NULL;
	struct request_sock *req;
	bool want_cookie = false;
	struct dst_entry *dst;
    /*
     * 如果启用了cookie机制，则会在第三步收到ACK的时候在tcp_v4_syn_recv_sock中
     * 的cookie_v4_check对之前发送的ack+syn进行检查，检查过程见cookie_v4_check
     */
	struct flowi fl;

	/* TW buckets are converted to open requests without
	 * limitations, they conserve resources and peer is
	 * evidently real one.
	 */
	if ((net->ipv4.sysctl_tcp_syncookies == 2 || // sysctl_tcp_syncookies=2无条件生成syncookie
	     inet_csk_reqsk_queue_is_full(sk)) && !isn) { // 或者半连接队列太长,并且当前不是timewait
		want_cookie = tcp_syn_flood_action(sk, rsk_ops->slab_name); // sysctl_tcp_syncookies>0,并未当前socket打印一次告警
		if (!want_cookie) // 队列满了，但不使用syncookie，则丢弃
			goto drop;
	}

    /*
     * 如果连接队列长度已达到上限则丢弃当前连接请求.
     * 如果在接收到三次握手中最后的ACK后连接队列
     * 中没有空闲的位置，会忽略接收到的ACK包，连接
     * 建立会推迟，所以此时最好丢掉部分新的连接请
     * 求，空出资源以完成正在进行的连接建立过程。
     * 还要注意，这个判断并没有考虑半连接队列是否
     * 已满的问题。从这里可以看出，即使开启了
     * SYN cookies机制并不意味着一定可以完成连接的建立。
     */
	if (sk_acceptq_is_full(sk)) { //accept队列满
		NET_INC_STATS(sock_net(sk), LINUX_MIB_LISTENOVERFLOWS);
		goto drop;
	}

    /*
     * 可以接收并处理连接请求，调用inet_reqsk_alloc()分配一个连接请求
     * 块，用于保存连接请求信息，同时初始化在建立连接过程中用来发送
     * ACK、RST段的操作集合，以便在建立连接过程中能方便地调用这些接口
     */
    // rsk_ops  ===tcp_request_sock_ops
	req = inet_reqsk_alloc(rsk_ops, sk, !want_cookie); //分配request_sock， 进入TCP_NEW_SYN_RECV状态
	if (!req)
		goto drop;

    // af_ops====tcp_request_sock_ipv4_opss
	tcp_rsk(req)->af_specific = af_ops; //tcp_request_sock_ipv4_ops
	tcp_rsk(req)->ts_off = 0;
#if IS_ENABLED(CONFIG_MPTCP)
	tcp_rsk(req)->is_mptcp = 0;
#endif

    /*
     * 清除TCP选项后初始化mss_clamp和user_mss。
     */
	tcp_clear_options(&tmp_opt);
	tmp_opt.mss_clamp = af_ops->mss_clamp;
	tmp_opt.user_mss  = tp->rx_opt.user_mss;
    /*
     * 解析SYN段中的TCP选项
     */
	tcp_parse_options(sock_net(sk), skb, &tmp_opt, 0,
			  want_cookie ? NULL : &foc); // 开启syncookie后则不用考虑fastopen， syncookie不允许使用tcp扩展

	if (want_cookie && !tmp_opt.saw_tstamp) // 开启syncookie，但是不带timestamp
		tcp_clear_options(&tmp_opt); // s清除wscale，sack_ok等选项，因为没地方存


	if (IS_ENABLED(CONFIG_SMC) && want_cookie)
		tmp_opt.smc_ok = 0;

    /*
     * 初始化该连接中是否启用时间戳的选项tstamp_ok
     */
	tmp_opt.tstamp_ok = tmp_opt.saw_tstamp;
    /*
     * 根据接收到SYN段中的选项和序号来初始化连接请求块信息
     */
	tcp_openreq_init(req, &tmp_opt, skb, sk);
	inet_rsk(req)->no_srccheck = inet_sk(sk)->transparent;

	/* Note: tcp_v6_init_req() might override ir_iif for link locals */
	inet_rsk(req)->ir_iif = inet_request_bound_dev_if(sk, skb);

    /*
     * 初始化TCP层次的连接请求信息块，包括目的地址、源地址，
     * 并调用tcp_v4_save_options从IP层私有控制块中获取IP
     * 选项保存到传输控制块的opt中，包括MSS、窗口扩大
     * 因子、显式拥塞通知等
     */
	af_ops->init_req(req, sk, skb); //tcp_v4_init_req  会调用tcp_v4_save_options

	if (IS_ENABLED(CONFIG_MPTCP) && want_cookie)
		tcp_rsk(req)->is_mptcp = 0;

	if (security_inet_conn_request(sk, skb, req))
		goto drop_and_free;

	if (tmp_opt.tstamp_ok)
		tcp_rsk(req)->ts_off = af_ops->init_ts_off(net, skb);

	dst = af_ops->route_req(sk, &fl, req); //tcp_v4_route_req
	if (!dst)
		goto drop_and_free;

	if (!want_cookie && !isn) { //不需要生成syncookie，也不是从timewait recycle的新的sock
		/* Kill the following clause, if you dislike this way. */
        //如果没开启sysctl_tw_recycle和syncookie，最后1/4的syn请求需要验证过去的连接信?
        /*
         * 未启动syncookies的情况下受到synflood攻击，则丢弃接收到的段
         */
		if (!net->ipv4.sysctl_tcp_syncookies &&
		    (net->ipv4.sysctl_max_syn_backlog - inet_csk_reqsk_queue_len(sk) <
		     (net->ipv4.sysctl_max_syn_backlog >> 2)) &&
		    !tcp_peer_is_proven(req, dst)) {
			/* Without syncookies last quarter of
			 * backlog is filled with destinations,
			 * proven to be alive.
			 * It means that we continue to communicate
			 * to destinations, already remembered
			 * to the moment of synflood.
			 */
            //如果不存在tcp metric或者过去的连接信息则丢弃
			pr_drop_req(req, ntohs(tcp_hdr(skb)->source),
				    rsk_ops->family);
//            /*
//                1 tcp的option有 time stamp字段.
//                2 tcp_tw_recycle有设置。
//                3 在路由表中是否存在完全相同的流(如果打开了xfrm的话，
//                还要比较端口,默认xfrm应该是打开的)，如果存在则直接返回.
//                4 并且数据包的源地址和新请求的源地址相同.
//                5 根据路由表以及源地址能够查找到保存的peer
//                (这个可以看我以前的blog，也就是保存了一些连接统计信息).
//                6 当前时间(接收到syn)比最后一次的时间(time stamp)小于60秒.
//                7 已经存在peer的最近一次时间戳要大于当前请求进来的时间戳.
//                从上面可以看到，上面的条件中1/2都是 server端可以控制的，而其他的条件，
//                都是很容易就满足的，因此我们举个例子。
//                如果客户端是NAT出来的，并且我们server端有打开tcp_tw_recycle ,
//                并且time stamp也没有关闭，那么假设第一个连接进来，然后关闭，此时这个句柄处于time wait状态，然后很快(小于60秒)又一个客户端(相同的源地址，如果打开了xfrm还要相同的端口号)发一个syn包，此时linux内核就会认为这个数据包异常的，因此就会丢掉这个包,并发送rst。
//                而现在大部分的客户端都是NAT出来的，因此建议tw_recycle还
//                是关闭,或者说server段关闭掉time stamp(/proc/sys/net/ipv4/tcp_timestamps).
//               */
			goto drop_and_release;
		}

		isn = af_ops->init_seq(skb); // tcp_v4_init_sequence，根据四元组，随机数，当前高精度时间来生成isn
	}

	tcp_ecn_create_request(req, skb, sk, dst);

	if (want_cookie) {
        /*
         * 如果启动了syncookies，则每60秒警告一次可能受
         * synflood攻击，同时由客户端IP地址、客户端端口、
         * 服务器IP地址、服务器端口、客户端初始序列号
         * 等要素经hash运算后加密得到服务端初始化序列号
         */
        // 如果开启了syncookie选项，则需要检查收到的第三步ack和这个isn值是否一致
		isn = cookie_init_sequence(af_ops, sk, skb, &req->mss);
        // cookie_v4_init_sequence生成syncookie，并作为ack的起始序号
		req->cookie_ts = tmp_opt.tstamp_ok;
		if (!tmp_opt.tstamp_ok)
			inet_rsk(req)->ecn_ok = 0;
	}

	tcp_rsk(req)->snt_isn = isn;
	tcp_rsk(req)->txhash = net_tx_rndhash();
	tcp_openreq_init_rwin(req, sk, dst); // 设置初始化rwnd
	sk_rx_queue_set(req_to_sk(req), skb);
	if (!want_cookie) {
		tcp_reqsk_record_syn(sk, req, skb); // 如果设置保存TCP_SAVE_SYN标记，则保存
		fastopen_sk = tcp_try_fastopen(sk, skb, req, &foc, dst); // 验证后创建fastopen sock，并把数据部分放入接收队列中
	}
	if (fastopen_sk) { // 验证并创建fastsocket成功, 进入TCP_SYN_RCV状态
		af_ops->send_synack(fastopen_sk, dst, &fl, req,
				    &foc, TCP_SYNACK_FASTOPEN); // tcp_v4_send_synac
		/* Add the child socket directly into the accept queue */
        // 添加到等待accept的队列
		if (!inet_csk_reqsk_queue_add(sk, req, fastopen_sk)) {
			reqsk_fastopen_remove(fastopen_sk, req, false);
			bh_unlock_sock(fastopen_sk);
			sock_put(fastopen_sk);
			goto drop_and_free;
		}
		sk->sk_data_ready(sk);
		bh_unlock_sock(fastopen_sk);
		sock_put(fastopen_sk);
	} else {
		tcp_rsk(req)->tfo_listener = false;
		if (!want_cookie)
			inet_csk_reqsk_queue_hash_add(sk, req,
				tcp_timeout_init((struct sock *)req)); // 插入ehash，并设置定时器
		af_ops->send_synack(sk, dst, &fl, req, &foc,
				    !want_cookie ? TCP_SYNACK_NORMAL :
						   TCP_SYNACK_COOKIE); // tcp_v4_send_synack
		if (want_cookie) {
			reqsk_free(req); // 启用syncookie的话，可以直接释放req
			return 0;
		}
	}
	reqsk_put(req);
	return 0;

drop_and_release:
	dst_release(dst);
drop_and_free:
	__reqsk_free(req);
drop:
	tcp_listendrop(sk);
	return 0;
}
EXPORT_SYMBOL(tcp_conn_request);
