# Use Rsync to propagate all the changes in the scripts in this
# directory to the tester and the server.

. ./config.sh

rsync -tv -r ./ $TESTER_HOST:scripts
rsync -tv -r ./ $SERVER_HOST:scripts
