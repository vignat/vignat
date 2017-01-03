#!/bin/bash
# See http://dpdk.org/doc/quick-start

# DPDK release to install
DPDK_RELEASE=16.07


pushd $HOME >> /dev/null

# Check if it's already installed; we manually create a file with the version
if [ ! -f dpdk/.version ] || [ "$(cat dpdk/.version)" != $DPDK_RELEASE ]; then
    echo "[init] DPDK not found or obsolete, installing..."

    # Install required packages
    sudo apt-get install -yqq wget build-essential linux-headers-`uname -r`

    # If the directory already exists, assume it's an older version, delete it
    if [ -d dpdk ]; then
        rm -rf dpdk
    fi

    # Download DPDK
    wget http://static.dpdk.org/rel/dpdk-$DPDK_RELEASE.tar.xz
    tar xf dpdk-$DPDK_RELEASE.tar.xz
    mv dpdk-$DPDK_RELEASE dpdk
    rm dpdk-$DPDK_RELEASE.tar.xz

    # Compile it
    cd dpdk
    sed -ri 's,(PMD_PCAP=).*,\1y,' config/common_linuxapp
    make config T=x86_64-native-linuxapp-gcc
    make install -j T=x86_64-native-linuxapp-gcc DESTDIR=.

    # Write out the version for next run
    echo $DPDK_RELEASE > .version
fi

popd >> /dev/null
