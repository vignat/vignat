#!/bin/bash

# Removes software limits to unlock the full power of NetFilter

# Parameter:
# $1: The interface that will be used to transmit packets


if [ -z $1 ]; then
    echo "[util] No interface given in netfilter-unlock" 1>&2
    exit 1
fi



# 4KB send buffer, 20,480 connections max at worst case
echo 83886080  > /proc/sys/net/core/wmem_max
echo 83886080  > /proc/sys/net/core/wmem_default

# 16KB receive buffer, 20,480 connections max at worst case
echo 335544320 > /proc/sys/net/core/rmem_max
echo 335544320 > /proc/sys/net/core/rmem_default

# Max open files
# already bigger: echo 65536 > /proc/sys/fs/filemax

# Fast port recycling (TIME_WAIT)
echo 1 >/proc/sys/net/ipv4/tcp_tw_recycle
echo 1 >/proc/sys/net/ipv4/tcp_tw_reuse

# TIME_WAIT buckets increased
# already bigger: echo 65536 > /proc/sys/net/ipv4/tcp_max_tw_buckets

# FIN timeout decreased
echo 15 > /proc/sys/net/ipv4/tcp_fin_timeout

# SYN backlog increased
echo 65536 > /proc/sys/net/ipv4/tcp_max_syn_backlog

# SYN cookies enabled
echo 1 > /proc/sys/net/ipv4/tcp_syncookies

# Local port range maximized
echo "1024 65535" > /proc/sys/net/ipv4/ip_local_port_range

# Netdev backlog increased
echo 100000 > /proc/sys/net/core/netdev_max_backlog

# Interface transmit queuelen increased
ifconfig $1 txqueuelen 10000
