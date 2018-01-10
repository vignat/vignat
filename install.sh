#!/bin/bash
# Tested on Ubuntu 16.04 and the Linux Subsystem for Windows

# Bash "strict mode"
set -euxo pipefail

# Setup

VNDSDIR=$(cd $(dirname "$0") && pwd)
BUILDDIR="$HOME"
cd "$BUILDDIR"


### General

sudo apt-get install -y cmake wget build-essential curl git subversion python parallel opam

opam init -y
opam switch 4.06.0
echo 'PATH=$PATH:'"$HOME/.opam/system/bin" >> ~/.profile
echo ". $HOME/.opam/opam-init/init.sh" >> ~/.profile
. ~/.profile


### Z3 v4.5

# VeriFast requires Z3 in ocamlfind; install it now so that it puts itself in ocamlfind
opam install ocamlfind -y

git clone --depth 1 --branch z3-4.5.0 https://github.com/Z3Prover/z3
cd z3
python scripts/mk_make.py --ml
cd build
make
sudo "PATH=$PATH" make install # need the path for ocamlfind
cd ../..


### KLEE

sudo apt-get install -y bison flex zlib1g-dev libncurses5-dev libcap-dev \
                        python-minimal

svn co https://llvm.org/svn/llvm-project/llvm/tags/RELEASE_342/final llvm
svn co https://llvm.org/svn/llvm-project/cfe/tags/RELEASE_342/final llvm/tools/clang
svn co https://llvm.org/svn/llvm-project/compiler-rt/tags/RELEASE_342/final llvm/projects/compiler-rt
svn co https://llvm.org/svn/llvm-project/libcxx/tags/RELEASE_342/final llvm/projects/libcxx
cd llvm
./configure --enable-optimized --disable-assertions --enable-targets=host --with-python='/usr/bin/python2'
make -j $(nproc)
echo 'PATH=$PATH:'"$BUILDDIR/llvm/Release/bin" >> ~/.profile
. ~/.profile
cd ..

git clone --depth 1 --branch klee_uclibc_v1.0.0 https://github.com/klee/klee-uclibc.git
cd klee-uclibc
./configure \
 --make-llvm-lib \
 --with-llvm-config="../llvm/Release/bin/llvm-config" \
 --with-cc="../llvm/Release/bin/clang"
make -j $(nproc)
cd ..

git clone --depth 1 --branch timed-access-dirty-rebased https://github.com/SolalPirelli/klee.git
cd klee
mkdir build
cd build
cmake \
 -DENABLE_UNIT_TESTS=OFF \
 -DBUILD_SHARED_LIBS=OFF \
 -DENABLE_KLEE_ASSERTS=OFF \
 -DLLVM_CONFIG_BINARY=$BUILDDIR/llvm/Release/bin/llvm-config \
 -DLLVMCC=$BUILDDIR/llvm/Release/bin/clang \
 -DLLVMCXX=$BUILDDIR/llvm/Release/bin/clang++ \
 -DENABLE_SOLVER_Z3=ON \
 -DENABLE_KLEE_UCLIBC=ON \
 -DKLEE_UCLIBC_PATH=$BUILDDIR/klee-uclibc \
 -DENABLE_POSIX_RUNTIME=ON \
 ..
make
echo 'PATH=$PATH:'"$BUILDDIR/klee/build/bin" >> ~/.profile
echo "export KLEE_INCLUDE=$BUILDDIR/klee/include" >> ~/.profile
. ~/.profile
cd ../..


### VeriFast

sudo apt-get install -y --no-install-recommends \
                     ca-certificates m4 \
                     ocaml-native-compilers gcc camlp4 patch unzip libgtk2.0-dev \
                     valac gtksourceview2.0-dev \
                     liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev

# Not mentioned by VeriFast's readme, required anyway
opam install ocamlfind camlp4 -y

git clone --depth 1 --branch export_path_conditions https://github.com/SolalPirelli/verifast
cd verifast/src
make verifast # should be just "make" but vfide fails (even with lablgtk)
echo 'PATH=$PATH:'"$BUILDDIR/verifast/bin" >> ~/.profile
. ~/.profile
cd ../..


### DPDK

# On the Linux subsystem for Windows, uname -r includes a "-Microsoft" token
KERNEL_VER=$(uname -r | sed 's/-Microsoft//')

sudo apt-get install -y "linux-headers-$KERNEL_VER"

wget -O dpdk.tar.xz http://static.dpdk.org/rel/dpdk-16.07.tar.xz
tar xf dpdk.tar.xz
rm dpdk.tar.xz
mv dpdk-16.07 dpdk

echo 'export RTE_TARGET=x86_64-native-linuxapp-gcc' >> ~/.profile
echo "export RTE_SDK=$BUILDDIR/dpdk" >> ~/.profile
. ~/.profile

cd dpdk
sed -ri 's,(PMD_PCAP=).*,\1y,' config/common_linuxapp

case $(uname -r) in
  *Microsoft*)
    # Fix the kernel dir, since the Linux subsystem for Windows doesn't have an actual Linux kernel...
    sudo apt install "linux-headers-$KERNEL_VER-generic"
    export RTE_KERNELDIR="/usr/src/linux-headers-$KERNEL_VER-generic/"
  ;;
esac

make config T=x86_64-native-linuxapp-gcc
make install -j T=x86_64-native-linuxapp-gcc DESTDIR=.

# Apply the Vigor patches ( :( )
patch -p1 < "$VNDSDIR/dpdk.patch"

# Enable atomic intrinsics, otherwise it uses inline ASM which KLEE doesn't support
sed -i 's/CONFIG_RTE_FORCE_INTRINSICS=n/CONFIG_RTE_FORCE_INTRINSICS=y/' x86_64-native-linuxapp-gcc/.config
# Use stacks instead of rings for mbuf pools, so that an [allocate+free] operation is idempotent
sed -i 's/CONFIG_RTE_MBUF_DEFAULT_MEMPOOL_OPS="ring_mp_mc"/CONFIG_RTE_MBUF_DEFAULT_MEMPOOL_OPS="stack"/' x86_64-native-linuxapp-gcc/.config
# 2 ports maximum... for now
sed -i 's/CONFIG_RTE_MAX_ETHPORTS=32/CONFIG_RTE_MAX_ETHPORTS=2/' x86_64-native-linuxapp-gcc/.config
# Rebuild
make install -j T=x86_64-native-linuxapp-gcc DESTDIR=.

cd ..


### Validator dependencies

opam install ocamlfind core sexplib menhir -y
