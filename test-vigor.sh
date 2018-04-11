#!/bin/bash

. paths.sh

set -euxo pipefail


# TODO: make verify-* (use travis jobs to parellelize)
pushd nf/vignat
  make verify-dpdk
popd
pushd nf/bridge
  make verify-dpdk
popd

echo "All symbex succeeded"

pushd nf
  make verifast
popd

echo "All verifast checks pass"
