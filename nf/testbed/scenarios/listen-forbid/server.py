import sys
from scapy.all import *
import time

time.sleep(0.1)
sendp(Ether(dst='08:00:27:00:44:71')/IP(dst='192.168.33.2')/TCP(sport=8888, dport=260), iface='eth1')
