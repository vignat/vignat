#!/bin/bash
. ./config.sh

echo "[init] Cloning scripts..."
cp ../../../install.sh . # also include the install script for DPDK
for h in $TESTER_HOST; do
    rsync -q -t -r --exclude '*.log' --exclude '*.results' ./ $h:scripts
done
rm install.sh

echo "[init] Initializing all machines..."
ssh $TESTER_HOST 'bash ~/scripts/init-machines/tester.sh'
#ssh $SERVER_HOST 'bash ~/scripts/init-machines/server.sh'
. ./init-machines/middlebox.sh
