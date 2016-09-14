. ./config.sh

ssh $TESTER_HOST 'sudo sh ~/tester-provision-for-stub.sh'
ssh $SERVER_HOST 'sudo sh ~/server-provision-for-stub.sh'

