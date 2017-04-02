#!/bin/bash

# pktgen release to install
PKTGEN_RELEASE=3.0.13


pushd $HOME >> /dev/null

# Check if it's already installed; we manually create a file with the version
if [ ! -f pktgen/.version -o "$(cat pktgen/.version)" != $PKTGEN_RELEASE ]; then
    echo "[init] pktgen not found or obsolete, installing..."

    # If the directory already exists, assume it's an older version, delete it
    if [ -d pktgen ]; then
        rm -rf pktgen
    fi

    # Download pktgen
    wget http://dpdk.org/browse/apps/pktgen-dpdk/snapshot/pktgen-$PKTGEN_RELEASE.tar.gz
    tar xf pktgen-$PKTGEN_RELEASE.tar.gz
    mv pktgen-$PKTGEN_RELEASE pktgen
    rm pktgen-$PKTGEN_RELEASE.tar.gz
    cd pktgen

    # Patch it to support 65536 flows instead of 8192
    patch -p1 -i ~/scripts/init-machines/pktgen.patch

    # Define DPDK environment variables for compilation
    export RTE_SDK=$HOME/dpdk
    export RTE_TARGET=x86_64-native-linuxapp-gcc

    # Compile it
    make -j

    # Write out the version for next run
    echo $PKTGEN_RELEASE > .version
fi

popd >> /dev/null
