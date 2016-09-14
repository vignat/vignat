
. ./config.sh

. ./dpdk-setup-functions.sh

set_numa_pages
load_igb_uio_module

sudo ifconfig $TESTER_DEVICE_INTERNAL down
sudo ifconfig $TESTER_DEVICE_EXTERNAL down

bind_nics_to_igb_uio $TESTER_PCI_INTERNAL $TESTER_PCI_EXTERNAL
