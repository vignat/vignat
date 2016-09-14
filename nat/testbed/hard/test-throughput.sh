. ./config.sh

# STUB
bash ./provision-stub.sh
bash ./redeploy-stub.sh
(./run-stub.sh $PWD 0<&- &>stb.log) &

# Wait until the application loads up
sleep 5

ssh $CLIENT_HOST "bash ~/throughput-pktsize.sh $SERVER_IP_INDIRECT 5 10"
scp $CLIENT_HOST:result.txt ./stub-thru-pktsize.txt

sudo pkill -9 nat

sleep 2

# NAT
bash ./provision-nat.sh
bash ./redeploy-nat.sh
(./run-nat.sh $PWD 0<&- &>nat.log) &

sleep 5

ssh $CLIENT_HOST "bash ~/throughput-pktsize.sh $SERVER_IP_INDIRECT 5 10"
scp $CLIENT_HOST:result.txt ./nat-thru-pktsize.txt

sudo pkill -9 nat

sleep 2

# NetFilter
sudo ./nf-nat.sh 0<&- &>nfn.log

sleep 10

ssh $CLIENT_HOST "bash ~/throughput-pktsize.sh $SERVER_IP_INDIRECT 5 10"
scp $CLIENT_HOST:result.txt ./nf-thru-pktsize.txt

# Direct
ssh $CLIENT_HOST "bash ~/throughput-pktsize.sh $SERVER_IP_DIRECT 5 10"
scp $CLIENT_HOST:result.txt ./direct-thru-pktsize.txt
