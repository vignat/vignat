#!/bin/bash

echo "[init] Initializing server..."

sudo apt-get -qq update

sudo apt-get install -yqq \
    tcpdump hping3 iperf3 apache2 netperf
