#!/bin/bash

echo "[init] Initializing middlebox..."

sudo apt-get -qq update

sudo apt-get install -yqq \
    tcpdump git libpcap-dev \
    linux-headers-3.13.0-93 \
    libglib2.0-dev daemon iperf3 netperf tmux

pushd "$HOME"
  bash vnds/install.sh dpdk-only
popd
