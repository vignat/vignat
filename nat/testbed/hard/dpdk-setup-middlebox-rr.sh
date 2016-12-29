# Setup middlebox for request-response(ping-pong) scenario in DPDK compatible mode
# (unbind the necessary ifaces from the kernel)

. ./config.sh

. ./dpdk-setup-functions.sh

set_numa_pages
load_igb_uio_module

sudo ifconfig $MB_DEVICE_EXTERNAL down
sudo ifconfig $MB_DEVICE_INTERNAL down
sudo ifconfig $MB_DEVICE_TO_SRV down

#$RTE_SDK/tools/dpdk-devbind.py -u $MB_PCI_EXTERNAL
bind_nics_to_igb_uio $MB_PCI_EXTERNAL
bind_nics_to_igb_uio $MB_PCI_INTERNAL
bind_nics_to_igb_uio $MB_PCI_TO_SRV
