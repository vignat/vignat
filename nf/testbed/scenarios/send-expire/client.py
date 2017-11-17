import sys
import time
from scapy.all import *

sendp(Ether(dst='08:00:27:00:44:72')/IP(dst='192.168.33.10')/TCP(dport=8888), iface='eth1')

def receive(packet):
    p = packet[0][1]
    if p.src == '192.168.33.10' and p.load == 'expired':
        sys.exit(1)

sniff(filter='tcp', prn=receive, timeout=12, iface='eth1')

sys.exit(0)
