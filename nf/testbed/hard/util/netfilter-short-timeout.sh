
. ./util/functions.sh 

TIMEOUT=$1

sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_frag6_timeout $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_generic_timeout $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_icmp_timeout $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_icmpv6_timeout $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_max_retrans 0
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_close $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_close_wait $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_established $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_fin_wait $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_last_ack $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_max_retrans $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_syn_recv $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_syn_sent $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_time_wait $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_tcp_timeout_unacknowledged $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_udp_timeout $TIMEOUT
sudo_overwrite /proc/sys/net/netfilter/nf_conntrack_udp_timeout_stream2 $TIMEOUT
