
. ./config.sh

. ./dpdk-setup-functions.sh

set_numa_pages
load_igb_uio_module

sudo ifconfig $MB_DEVICE_INTERNAL down
sudo ifconfig $MB_DEVICE_TO_SRV down

bind_nics_to_igb_uio $MB_PCI_INTERNAL
bind_nics_to_igb_uio $MB_PCI_TO_SRV
