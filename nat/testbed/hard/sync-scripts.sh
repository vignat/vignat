. ./config.sh

rsync -tv -r ./ $TESTER_HOST:scripts
rsync -tv -r ./ $SERVER_HOST:scripts
