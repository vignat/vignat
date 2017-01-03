#!/bin/bash
. ./config.sh

echo "[init] Cloning scripts..."
rsync -tv -r ./ $TESTER_HOST:scripts
rsync -tv -r ./ $SERVER_HOST:scripts

echo "[init] Initializing all machines..."
ssh $TESTER_HOST 'bash ~/scripts/init-machines/tester.sh'
ssh $SERVER_HOST 'bash ~/scripts/init-machines/server.sh'
. ./init-machines/middlebox.sh
