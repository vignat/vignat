#!/bin/bash
# Install all the necessary package for the server to participate
# in the performance testing.
sudo apt-get update && sudo apt-get install -y tcpdump hping3 iperf3 apache2 netperf
