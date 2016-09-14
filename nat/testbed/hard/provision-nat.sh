. ./config.sh

ssh $TESTER_HOST 'sudo sh ~/tester-provision-for-nat.sh'
ssh $SERVER_HOST 'sudo sh ~/server-provision-for-nat.sh'

