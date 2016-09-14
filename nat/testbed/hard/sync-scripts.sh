. ./config.sh

rsync -r ./ $TESTER_HOST:scripts
rsync -r ./ $SERVER_HOST:scripts
