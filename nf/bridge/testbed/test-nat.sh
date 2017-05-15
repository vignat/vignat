#!/bin/bash

vagrant up
vagrant ssh -c 'wget -O /dev/null -T 1 -t 1 192.168.33.10' client
if [ $? -eq 0 ]; then
    echo "NAT works!"
else
    echo "Something wrong"
fi
