apt-get update
apt-get install -y tcpdump hping3 python-scapy wget linux-headers-3.13.0-86 linux-headers-3.13.0-86-generic libpcap-dev git
ip route add 192.168.33.0/24 via 192.168.40.2 dev eth1
arp -s 192.168.40.2 08:00:27:00:44:72
#hping3 192.168.33.10 -k -p 47882 -s 0

mkdir -p /mnt/huge
chmod 777 /mnt/huge
echo "vm.nr_hugepages=256" >> /etc/sysctl.conf
echo "huge /mnt/huge hugetlbfs defaults 0 0" >> /etc/fstab
# reload sysctl config without reboot
sysctl --system
mount huge
# the above setting nr_hugepages does not work for some reason
echo 256 > /sys/kernel/mm/hugepages/hugepages-2048kB/nr_hugepages

cd ~vagrant
git clone --depth 1 --branch v16.07-rc1 http://dpdk.org/git/dpdk
git clone --depth 1 --branch pktgen-3.0.02 http://dpdk.org/git/apps/pktgen-dpdk

export RTE_SDK=~vagrant/dpdk
export RTE_TARGET=x86_64-native-linuxapp-gcc

cd $RTE_SDK
make install T=$RTE_TARGET

cd ~vagrant/pktgen-dpdk
make

echo "export RTE_SDK=$RTE_SDK" >> ~vagrant/.bashrc
echo "export RTE_TARGET=$RTE_TARGET" >> ~vagrant/.bashrc
echo "sudo /sbin/modprobe uio" >> ~vagrant/.bashrc
echo "sudo $PWD/setup.sh" >> ~vagrant/.bashrc

. setup.sh
/sbin/modprobe uio
ifconfig eth1 down
${RTE_SDK}/tools/dpdk_nic_bind.py -b igb_uio 0000:00:08.0

# runstring: sudo ./app/app/x86_64-native-linuxapp-gcc/pktgen -c 0x1 -n 2 -- -P -m "0.0"
