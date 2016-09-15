. ./config.sh

echo "syncing scripts"
. ./sync-scripts.sh

echo "provision tester for STUB scenario"
ssh $TESTER_HOST 'sudo sh ~/scripts/tester-provision-rr-for-stub.sh'
echo "provision server for STUB scenario"
ssh $SERVER_HOST 'sudo sh ~/scripts/server-provision-rr-for-stub.sh'

