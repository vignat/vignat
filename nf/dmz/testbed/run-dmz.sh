#!/bin/bash

EXPTIME=10
MAX_FLOWS=1024

sudo /dmz/build/dmz -c 0x01 -n 2 -- --expire 10 --max-flows 1024 --extip 192.168.33.2 --eth-dest 0,08:00:27:53:8b:38 --eth-dest 1,08:00:27:c1:13:47

