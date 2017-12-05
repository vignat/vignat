import sys
from scapy.all import *

def receive(packet):
    if packet[0][1].src == '192.168.33.2':
        sendp(Ether(dst='08:00:27:00:44:71')/IP(dst='192.168.33.2')/TCP(sport=8888, dport=packet[0][1].sport)/'okay', iface='eth1')
        sys.exit(0)

sniff(filter='tcp and port 8888', prn=receive, timeout=0.2)

sys.exit(1)
