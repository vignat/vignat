. ./config.sh

echo "syncing scripts"
. ./sync-scripts.sh

echo "Provisioning tester for NAT scenario"
ssh $TESTER_HOST 'sudo sh ~/scripts/tester-provision-rr-for-nat.sh'
echo "Provisioning server for NAT scenario"
ssh $SERVER_HOST 'sudo sh ~/scripts/server-provision-rr-for-nat.sh'

