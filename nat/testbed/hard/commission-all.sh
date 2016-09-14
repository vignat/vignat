. ./config.sh

echo "copying all the scripts to $TESTER_HOST and $SERVER_HOST"
. ./sync-scripts.sh

echo "running commission on tester"
ssh $TESTER_HOST 'sh ~/scripts/tester-commission.sh'

echo "running commission on server"
ssh $SERVER_HOST 'sh ~/scripts/server-commission.sh'

echo "runing commission on middlebox"
. ./nat-commission.sh
