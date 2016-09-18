cd ~/pktgen
sleep 9999999999 | ./app/app//x86_64-native-linuxapp-gcc/pktgen -c 0x1f -n 3 -- -P -m "[1-2:3-4].0" -f ../scripts/pktgen-scripts/provision-rr.lua -G &> ./pktgen-log.txt
disown %1
