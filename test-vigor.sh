#!/bin/bash

. paths.sh

pushd nf/vignat
  make verify-dpdk
popd
pushd nf/bridge
  make verify-dpdk
popd

echo "All symbex succeeded"
