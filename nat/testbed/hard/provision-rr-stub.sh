# Provision the requrest-responce (ping-pong) scenario with the middlebox
# running a plain forwarding (no-op)

. ./config.sh

echo "syncing scripts"
. ./sync-scripts.sh

echo "provision tester for STUB scenario"
ssh $TESTER_HOST 'sudo bash ~/scripts/tester-provision-rr-for-stub.sh'
echo "provision server for STUB scenario"
ssh $SERVER_HOST 'sudo bash ~/scripts/server-provision-rr-for-stub.sh'

