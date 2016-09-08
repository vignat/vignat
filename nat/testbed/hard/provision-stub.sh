. ./config.sh

ssh $CLIENT_HOST 'sudo sh ~/client-provision-for-stub.sh'
ssh $SERVER_HOST 'sudo sh ~/server-provision-for-stub.sh'

