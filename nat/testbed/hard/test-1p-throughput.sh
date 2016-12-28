. ./config.sh

mkdir -p results-1p-throughput

. ./sync-scripts.sh

sudo pkill -9 nat

bash provision-lb.sh
bash dpdk-setup-middlebox-lb.sh

TEST_FILE="$HOME/scripts/pktgen-scripts/find-breaking-point-mf.lua"

if false
then

echo "[TT]testing STUB"
# STUB
#bash ./provision-stub.sh
bash ./redeploy-stub.sh
(./run-stub.sh $PWD 0<&- &>stb.log) &

# Wait until the application loads up
#sleep 5
sleep 20

ssh $TESTER_HOST "bash ~/scripts/run-pktgen.sh $TEST_FILE"
scp $TESTER_HOST:pktgen/multi-flows.txt ./results-1p-throughput/stub-rt-mf.txt

sudo pkill -9 nat

#sleep 2
sleep 10
fi

echo "[TT]testing VigNAT"
# NAT
(./run-nat-lb.sh $PWD 10 61000 0<&- &>nat.log) &

#sleep 5
sleep 20

ssh $TESTER_HOST "bash ~/scripts/run-pktgen.sh $TEST_FILE"
scp $TESTER_HOST:pktgen/multi-flows.txt ./results-1p-throughput/vig-nat-rt.txt

sudo pkill -9 nat

#sleep 2
sleep 10

echo "[TT]testing optimized VigNAT"
# NAT
(./run-opt-nat-lb.sh $PWD 10 61000 0<&- &>nat.log) &

#sleep 5
sleep 20

ssh $TESTER_HOST "bash ~/scripts/run-pktgen.sh $TEST_FILE"
scp $TESTER_HOST:pktgen/multi-flows.txt ./results-1p-throughput/vig-opt-nat-rt.txt

sudo pkill -9 nat

#sleep 2
sleep 10

echo "[TT]testing NetFilter"
# NetFilter
sudo ./nf-nat-lb.sh 0<&- &>nfn.log

#sleep 10
sleep 30

ssh $TESTER_HOST "bash ~/scripts/run-pktgen.sh $TEST_FILE"
scp $TESTER_HOST:pktgen/multi-flows.txt ./results-1p-throughput/nf-nat-rt.txt

