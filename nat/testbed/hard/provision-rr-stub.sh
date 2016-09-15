. ./config.sh

ssh $TESTER_HOST 'sudo sh ~/tester-provision-rr-for-stub.sh'
ssh $SERVER_HOST 'sudo sh ~/server-provision-rr-for-stub.sh'

