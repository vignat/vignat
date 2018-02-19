#!/bin/bash
. ./config.sh

echo "[init] Cloning scripts..."
cp ../../../install.sh . # also include the install script for DPDK
cp -r ../../../install . # and the patch directory it uses
for h in $TESTER_HOST; do
    rsync -q -t -r --exclude '*.log' --exclude '*.results' ./ $h:scripts
done
rm install.sh
rm -rf install

echo "[init] Initializing all machines..."
ssh $TESTER_HOST 'bash ~/scripts/init-machines/tester.sh'
#ssh $SERVER_HOST 'bash ~/scripts/init-machines/server.sh'
. ./init-machines/middlebox.sh
