#!/bin/bash

. ./config.sh

. /home/necto/vnds/nat/testbed/hard/redeploy-nat.sh
daemon /home/necto/vnds/nat/testbed/hard/run-nat.sh /home/necto/vnds/nat/testbed/hard
