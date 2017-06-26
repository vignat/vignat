#!/bin/bash

rm -f result.txt

serv=192.168.33.10
times=100

for interval in 20 30 40 45 50 55 60 70 100 150 300; do
  for i in $(seq 1 $times); do
    sleep 2
    rrr=$(sudo hping3 $serv -i u$interval -k -s 3453 -n -p 80 -q -c 10000 2>&1 | tail -n3 | head -n1 | awk '{print $7;}' | sed -e 's/%//')
    rez[$i]=$rrr
    echo "$interval $rrr" >> result.txt
  done
  echo "for $interval : ${rez[@]}"
done

