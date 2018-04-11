#!/bin/bash

. install-generic.sh --force
. install-dpdk.sh

sudo rm -rf /var/lib/apt/lists/*
