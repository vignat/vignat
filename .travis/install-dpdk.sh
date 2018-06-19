#!/bin/bash

VNDSDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
BUILDDIR=`pwd`
PATHSFILE="$BUILDDIR/paths.sh"

sudo sh -c 'echo "deb http://ch.archive.ubuntu.com/ubuntu/ xenial-updates main restricted" >> /etc/apt/sources.list'

sudo apt-get update --allow-unauthenticated

# On the Linux subsystem for Windows, uname -r includes a "-Microsoft" token
KERNEL_VER=$(uname -r | sed 's/-Microsoft//')

# Install the right headers; we do *not* install headers on Docker since it uses the underlying kernel
if [ "$OS" = 'microsoft' ]; then
    # Fix the kernel dir, since the Linux subsystem for Windows doesn't have an actual Linux kernel...
    sudo apt install "linux-headers-$KERNEL_VER-generic"
    export RTE_KERNELDIR="/usr/src/linux-headers-$KERNEL_VER-generic/"
elif [ "$OS" = 'linux' -o "$OS" = 'docker' ]; then
    sudo apt-get install -y --allow-unauthenticated "linux-headers-$KERNEL_VER"
fi

### DPDK
DPDK_RELEASE='17.11'

pushd "$BUILDDIR"
if [ ! -f dpdk/.version ] || [ "$(cat dpdk/.version)" != "$DPDK_RELEASE" ]; then
    rm -rf dpdk # in case it already exists

    wget -O dpdk.tar.xz "https://fast.dpdk.org/rel/dpdk-$DPDK_RELEASE.tar.xz"
    tar xf dpdk.tar.xz
    rm dpdk.tar.xz
    mv "dpdk-$DPDK_RELEASE" dpdk

    echo 'export RTE_TARGET=x86_64-native-linuxapp-gcc' >> "$PATHSFILE"
    echo "export RTE_SDK=$BUILDDIR/dpdk" >> "$PATHSFILE"
    . "$PATHSFILE"

    pushd dpdk
    # Apply the Vigor patches
    for p in "$VNDSDIR/install/"dpdk.*.patch; do
        patch -p1 < "$p"
    done

    make config T=x86_64-native-linuxapp-gcc
    make install -j $(nproc) T=x86_64-native-linuxapp-gcc DESTDIR=.

    echo "$DPDK_RELEASE" > .version
    popd
fi
popd
