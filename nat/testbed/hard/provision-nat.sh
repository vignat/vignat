. ./config.sh

ssh $TESTER_HOST 'sudo sh ~/tester-provision-rr-for-nat.sh'
ssh $SERVER_HOST 'sudo sh ~/server-provision-rr-for-nat.sh'

