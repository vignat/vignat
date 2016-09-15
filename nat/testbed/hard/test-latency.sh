. ./config.sh

mkdir -p latency-results

. ./sync-scripts.sh

echo "testing STUB"
# STUB
bash ./provision-rr-stub.sh
bash ./redeploy-stub-rr.sh
(./run-stub-rr.sh $PWD 0<&- &>stb.log) &

# Wait until the application loads up
#sleep 5
sleep 20

ssh $TESTER_HOST "bash ~/scripts/latency-mf.sh /home/necto/lat-res-stub.txt"
scp $TESTER_HOST:lat-res-stub.txt ./latency-results/stub.txt

sudo pkill -9 nat

#sleep 2
sleep 10

echo "testing VigNAT"
# NAT
bash ./provision-rr-nat.sh
bash ./redeploy-nat-rr.sh
(./run-nat-rr.sh $PWD 25 30000 0<&- &>nat.log) &

#sleep 5
sleep 20

ssh $TESTER_HOST "bash ~/scripts/latency-mf.sh /home/necto/lat-res-nat.txt"
scp $TESTER_HOST:lat-res-nat ./latency-results/vig-nat.txt

sudo pkill -9 nat

#sleep 2
sleep 10

echo "testing NetFilter"
# NetFilter
sudo ./nf-nat-rr.sh 0<&- &>nfn.log

#sleep 10
sleep 30

ssh $TESTER_HOST "bash ~/scripts/latency-mf.sh /home/necto/lat-res-nf.txt"
scp $TESTER_HOST:lat-res-nf ./latency-results/nf-nat.txt

