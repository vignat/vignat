#!/usr/bin/python

"""
mynat.py: network with two nats in operation:
nat1 is the nat being tested,
nat2 NetFilter standard reference nat


           h0
           |
           s0
           |
    ----------------
    |              |
   nat1           nat2
    |              |
   s1              s2
    |              |
   h1              h2

"""

from mininet.topo import Topo
from mininet.net import Mininet
from mininet.nodelib import NAT
from mininet.log import setLogLevel
from mininet.cli import CLI
from mininet.util import irange

class InternetTopo(Topo):
    "Single switch connected to n hosts."
    def __init__(self, n=2, **opts):
        Topo.__init__(self, **opts)

        # set up inet switch
        inetSwitch = self.addSwitch('s0')
        # add inet host
        inetHost = self.addHost('h0')
        self.addLink(inetSwitch, inetHost)

        # add local nets
        inetIntf = 'nat1-eth0'
        localIntf = 'nat1-eth1'
        localIP = '192.168.1.1'
        localSubnet = '192.168.1.0/24'
        natParams = { 'ip' : '%s/24' % localIP }
        # add NAT to topology
        nat = self.addNode('nat1')
        switch = self.addSwitch('s1')
        # connect NAT to inet and local switches
        self.addLink(nat, inetSwitch, intfName1=inetIntf)
        self.addLink(nat, switch, intfName1=localIntf, params1=natParams)
        # add host and connect to local switch
        host = self.addHost('h1',
                            ip='192.168.1.100/24',
                            defaultRoute='via %s' % localIP)
        self.addLink(host, switch)

        inetIntf = 'nat2-eth0'
        localIntf = 'nat2-eth1'
        localIP = '192.168.2.1'
        localSubnet = '192.168.2.0/24'
        natParams = { 'ip' : '%s/24' % localIP }
        # add NAT to topology
        nat = self.addNode('nat2', cls=NAT, subnet=localSubnet,
                           inetIntf=inetIntf, localIntf=localIntf)
        switch = self.addSwitch('s2')
        # connect NAT to inet and local switches
        self.addLink(nat, inetSwitch, intfName1=inetIntf)
        self.addLink(nat, switch, intfName1=localIntf, params1=natParams)
        # add host and connect to local switch
        host = self.addHost('h2',
                            ip='192.168.2.100/24',
                            defaultRoute='via %s' % localIP)
        self.addLink(host, switch)

def run():
    "Create network and run the CLI"
    topo = InternetTopo()
    net = Mininet(topo=topo)
    net.start()
    for h in net.hosts:
      if (h.name == 'nat1'):
        nat = h
        # Allocate hugepages for the dkdp application
        nat.cmdPrint('mkdir -p /mnt/huge')
        nat.cmdPrint('mount -t hugetlbfs nodev /mnt/huge')
        nat.cmdPrint('sh -c \'echo 384 > /sys/devices/system/node/node0/hugepages/hugepages-2048kB/nr_hugepages\'')
        # Drop the fantom reset packets
        nat.cmdPrint('iptables -A OUTPUT -p tcp --tcp-flags RST RST -j DROP ')
      elif (h.name == 'h0'):
        srv = h
        srv.cmdPrint('service apache2 restart')
      elif (h.name == 'h1'):
        clt = h
    runNatCmd = '/home/mininet/vnds/nat/build/nat -c 0x01 -n 2 --vdev=eth_pcap0,iface=nat1-eth0 --vdev=eth_pcap1,iface=nat1-eth1 -- -p 0x3 --wan 0 --extip %s --eth-dest 0,%s --eth-dest 1,%s &' % (nat.intfs[0].ip, srv.MAC(), clt.MAC())
    print runNatCmd
    CLI(net)
    net.stop()

if __name__ == '__main__':
    setLogLevel('info')
    run()
