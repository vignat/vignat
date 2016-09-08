. ./config.sh

ssh $CLIENT_HOST 'sudo sh ~/client-provision-for-nat.sh'
ssh $SERVER_HOST 'sudo sh ~/server-provision-for-nat.sh'

