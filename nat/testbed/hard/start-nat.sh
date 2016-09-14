#!/bin/bash

. ./config.sh

. ./redeploy-nat.sh
daemon ./run-nat.sh $PWD
