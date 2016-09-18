. ./config.sh

mkdir -p latency-results

. ./sync-scripts.sh

if false
then

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

fi

echo "testing VigNAT"
# NAT
bash ./provision-rr-nat.sh
bash ./redeploy-nat-rr.sh
(./run-nat-rr.sh $PWD 45 61000 0<&- &>nat.log) &

#sleep 5
sleep 20

ssh $TESTER_HOST "bash ~/scripts/latency-mf.sh /home/necto/lat-res-vig-nat.txt"
scp $TESTER_HOST:lat-res-vig-nat.txt ./latency-results/vig-nat.txt

sudo pkill -9 nat

if false
then

#sleep 2
sleep 10

echo "testing NetFilter"
# NetFilter
sudo ./nf-nat-rr.sh 0<&- &>nfn.log

#sleep 10
sleep 30

fi

ssh $TESTER_HOST "bash ~/scripts/latency-mf.sh /home/necto/lat-res-nf-nat.txt"
scp $TESTER_HOST:lat-res-nf-nat.txt ./latency-results/nf-nat.txt

