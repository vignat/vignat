. ./config.sh

scp config.sh $CLIENT_HOST:config.ch
scp client-commission.sh $CLIENT_HOST:client-commission.sh
scp client-provision-for-nat.sh $CLIENT_HOST:client-provision-for-nat.sh
ssh $CLIENT_HOST 'sh ~/client-commission.sh'

scp config.sh $SERVER_HOST:config.sh
scp server-commission.sh $SERVER_HOST:server-commission.sh
scp server-provision-for-nat.sh $SERVER_HOST:server-provision-for-nat.sh
ssh $SERVER_HOST 'sh ~/server-commission.sh'

. ./nat-commission.sh
