. ./config.sh

mkdir -p results

. ./sync-scripts.sh

echo "testing STUB"
# STUB
#bash ./provision-stub.sh
bash ./redeploy-stub.sh
(./run-stub.sh $PWD 0<&- &>stb.log) &

# Wait until the application loads up
#sleep 5
sleep 20

TEST_FILE="/home/necto/scripts/pktgen-scripts/regular-with-bin-mf.lua"

ssh $TESTER_HOST "bash ~/scripts/run-pktgen.sh $TEST_FILE"
scp $TESTER_HOST:pktgen/multi-flows.txt ./results/stub-rt-mf.txt

sudo pkill -9 nat

#sleep 2
sleep 10

echo "testing VigNAT"
# NAT
#bash ./provision-nat.sh
bash ./redeploy-nat.sh
(./run-nat.sh $PWD 1 30000 0<&- &>nat.log) &

#sleep 5
sleep 20

ssh $TESTER_HOST "bash ~/scripts/run-pktgen.sh $TEST_FILE"
scp $TESTER_HOST:pktgen/multi-flows.txt ./results/vig-nat-rt-mf.txt

sudo pkill -9 nat

#sleep 2
sleep 10

echo "testing NetFilter"
# NetFilter
sudo ./nf-nat.sh 0<&- &>nfn.log

#sleep 10
sleep 30

ssh $TESTER_HOST "bash ~/scripts/run-pktgen.sh $TEST_FILE"
scp $TESTER_HOST:pktgen/multi-flows.txt ./results/nf-nat-rt-mf.txt

