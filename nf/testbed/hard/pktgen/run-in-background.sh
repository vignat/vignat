#!/bin/bash
# Launch PktGen as a server listening 22022 in the background
# This script contains a piece of wisdom copy&pasted from StackOverflow.
# It is supposed to properly disconnect stdin and stdout using bahs pipe magic.

cd ~/pktgen && fifo=$(mktemp -u) && mkfifo "$fifo" && (rm "$fifo" && { sudo ./app/app/x86_64-native-linuxapp-gcc/pktgen -c 0x1f -n 3 -- -P -m "[1-2:3-4].0" -f $HOME/scripts/pktgen/provision-rr.lua -G < /dev/fd/1 3&>1 > ./pktgen-log.txt <&3 3<&-; } &) 3<> "$fifo" | :
