#!/bin/bash
. ./util/functions.sh

# Removes software limits to unlock the full power of NetFilter

# Parameter:
# $1: The interface that will be used to transmit packets


if [ -z $1 ]; then
    echo "[util] No interface given in netfilter-unlock" 1>&2
    exit 1
fi


# 4KB send buffer, 20,480 connections max at worst case
sudo_overwrite /proc/sys/net/core/wmem_max 83886080
sudo_overwrite /proc/sys/net/core/wmem_default 83886080

# 16KB receive buffer, 20,480 connections max at worst case
sudo_overwrite /proc/sys/net/core/rmem_max 335544320
sudo_overwrite /proc/sys/net/core/rmem_default 335544320

# Max open files
# already bigger: echo 65536 > /proc/sys/fs/filemax

# Fast port recycling (TIME_WAIT)
sudo_overwrite /proc/sys/net/ipv4/tcp_tw_recycle 1
sudo_overwrite /proc/sys/net/ipv4/tcp_tw_reuse 1

# TIME_WAIT buckets increased
# already bigger: echo 65536 > /proc/sys/net/ipv4/tcp_max_tw_buckets

# FIN timeout decreased
sudo_overwrite /proc/sys/net/ipv4/tcp_fin_timeout 15

# SYN backlog increased
sudo_overwrite /proc/sys/net/ipv4/tcp_max_syn_backlog 65536

# SYN cookies enabled
sudo_overwrite /proc/sys/net/ipv4/tcp_syncookies 1

# Local port range maximized
sudo_overwrite /proc/sys/net/ipv4/ip_local_port_range "1024 65535"

# Netdev backlog increased
sudo_overwrite /proc/sys/net/core/netdev_max_backlog 100000

# Interface transmit queuelen increased
sudo ifconfig $1 txqueuelen 10000
