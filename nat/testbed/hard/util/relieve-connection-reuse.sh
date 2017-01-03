#!/bin/bash
. ~/scripts/util/functions.sh

# Sacrifices some NetFilter fidelity to reuse connections faster

sudo_overwrite /proc/sys/net/ipv4/tcp_fin_timeout 5
sudo_overwrite /proc/sys/net/ipv4/tcp_tw_reuse 1
sudo_overwrite /proc/sys/net/ipv4/tcp_tw_recycle 1
