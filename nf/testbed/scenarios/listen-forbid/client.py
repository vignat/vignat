import sys
import time
from scapy.all import *

def receive(packet):
    if packet[0][1].src == '192.168.33.10':
        sys.exit(1)

sniff(filter='tcp', prn=receive, timeout=0.2, iface='eth1')

sys.exit(0)
