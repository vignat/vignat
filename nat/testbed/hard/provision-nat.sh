. ./config.sh

ssh $CLIENT_HOST 'sh ~/client-provision-for-nat.sh'
ssh $SERVER_HOST 'sh ~/server-provision-for-nat.sh'

./start-nat.sh
