#!/bin/bash
. ./config.sh

echo "[clean] Cleaning machines..."
ssh $TESTER_HOST "bash ~/scripts/clean/tester.sh"
. ./clean/middlebox.sh
