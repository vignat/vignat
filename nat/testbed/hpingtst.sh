#!/bin/bash

rm -f result.txt

serv=192.168.33.10

for interval in 10 15 20 30 40 50 60 70 100 150 300 500 1000; do
  for i in {0..10}; do
    sleep 2
    rrr=$(sudo hping3 $serv -i u$interval -k -s 3453 -n -p 80 -q -c 10000 2>&1 | tail -n3 | head -n1 | awk '{print $7;}' | sed -e 's/%//')
    rez[$i]=$rrr
    echo "$interval $rrr" >> result.txt
  done
  echo "for $interval : ${rez[@]}"
done

