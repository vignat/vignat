. ./config.sh

scp config.sh $TESTER_HOST:
scp tester-commission.sh $TESTER_HOST:
scp tester-provision-for-nat.sh $TESTER_HOST:
scp tester-provision-for-stub.sh $TESTER_HOST:
ssh $CLIENT_HOST 'sh ~/client-commission.sh'

scp config.sh $SERVER_HOST:
scp server-commission.sh $SERVER_HOST:
scp server-provision-for-nat.sh $SERVER_HOST:
scp server-provision-for-stub.sh $SERVER_HOST:
ssh $SERVER_HOST 'sh ~/server-commission.sh'

. ./nat-commission.sh
