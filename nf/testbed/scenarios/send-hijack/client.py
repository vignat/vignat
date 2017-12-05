import sys
import time
from scapy.all import *

sendp(Ether(dst='08:00:27:00:44:72')/IP(dst='192.168.33.10')/TCP(dport=8888), iface='eth1')

global good_packet
good_packet = False

def receive(packet):
    if packet[0][1].src == '192.168.33.3':
        sys.exit(1)

    if packet[0][1].src == '192.168.33.10':
        global good_packet
        good_packet = True

sniff(filter='tcp', prn=receive, timeout=0.1, iface='eth1')

if not good_packet:
    sys.exit(1)
