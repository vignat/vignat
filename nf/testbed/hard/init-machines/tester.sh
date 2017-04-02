#!/bin/bash

echo "[init] Initializing tester..."

sudo apt-get -qq update

sudo apt-get install -yqq \
    tcpdump hping3 python-scapy git \
    libpcap-dev libglib2.0-dev \
    daemon iperf3 netperf liblua5.2-dev \
    make binutils gcc \
    bc cmake

. ~/scripts/init-machines/install-dpdk.sh

. ~/scripts/init-machines/install-pktgen.sh

. ~/scripts/init-machines/install-moongen.sh
