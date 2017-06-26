#!/bin/bash
# Start the Vigor NAT in the background (as a daemon).

. ./hard/config.sh

. ./redeploy-nat.sh
daemon ./run-nat.sh $PWD
