#!/bin/bash
. ./config.sh

echo "[clean] Cleaning machines..."
ssh $SERVER_HOST 'bash ~/scripts/clean/server.sh'
. ./clean/middlebox.sh
