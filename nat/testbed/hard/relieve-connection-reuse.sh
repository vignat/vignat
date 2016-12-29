# Sacrifice some the NetFilter fidelity to dead connections
# (which is necessary only for accasional retransmissions),
# and allow it to faster reuse ports for new connections.

echo 5 > /proc/sys/net/ipv4/tcp_fin_timeout
echo 1 > /proc/sys/net/ipv4/tcp_tw_reuse
echo 1 > /proc/sys/net/ipv4/tcp_tw_recycle
