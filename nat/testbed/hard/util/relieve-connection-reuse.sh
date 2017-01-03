#!/bin/bash

# Sacrifices some NetFilter fidelity to reuse connections faster

echo 5 | sudo tee /proc/sys/net/ipv4/tcp_fin_timeout
echo 1 | sudo tee /proc/sys/net/ipv4/tcp_tw_reuse
echo 1 | sudo tee /proc/sys/net/ipv4/tcp_tw_recycle
