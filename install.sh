#!/bin/bash
# Tested on Ubuntu 16.04, Debian Stretch, and the Linux Subsystem for Windows

# Setup

VNDSDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
BUILDDIR=`pwd`

# Detect Docker or the Windows Subsystem for Linux
OS='linux'
if grep docker /proc/1/cgroup -qa; then
  OS='docker'
fi
case $(uname -r) in
  *Microsoft*)
    OS='windows'
    ;;
esac


if [ "$BUILDDIR" -ef "$VNDSDIR" ] && [ "$OS" != "docker" ]; then
  echo 'It is not recommented to install the dependencies into the project root directory.'
  echo "We recommend you to run the script from the parent directory like this: . $VNDSDIR/install.sh"
  read -p "Continue installing into $BUILDDIR? [y/n]" -n 1 -r
  echo # move to a new line
  if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    [[ "$0" = "$BASH_SOURCE" ]] && exit 1 || return 1 # handle exits from shell or function but don't exit interactive shell
  fi
fi

# Bash "strict mode"
set -euxo pipefail

PATHSFILE="$BUILDDIR/paths.sh"
echo '# The configuration paths for VNDS dependencies' > "$PATHSFILE"

### General

sudo apt-get update

# cmake for KLEE
# subversion for LLVM
# parallel for the Vigor Validator
# m4 for OCaml (not a dependency of opam but in practice it is)
sudo apt-get install -y \
                     bison flex zlib1g-dev libncurses5-dev libcap-dev cmake subversion `# for KLEE/LLVM` \
                     parallel `# for the Vigor Validator` \
                     opam m4 `# for OCaml; m4 is not a dependency in theory but it is in practice` \
                     libpcap-dev `# for DPDK` \
                     wget build-essential git python `# for more or less everything`

 # OCaml uses variables in its scripts without defining it first - we're in strict mode!
if [ -z ${PERL5LIB+x} ]; then
  export PERL5LIB=''
fi
if [ -z ${MANPATH+x} ]; then
  export MANPATH=''
fi

opam init -y
opam switch 4.06.0
echo 'PATH=$PATH:'"$HOME/.opam/system/bin" >> "$PATHSFILE"
echo ". $HOME/.opam/opam-init/init.sh" >> "$PATHSFILE"
. "$PATHSFILE"


### Z3 v4.5

# VeriFast requires Z3 in ocamlfind; install it now so that it puts itself in ocamlfind
# Num is required for Big_int
opam install ocamlfind num -y

git clone --depth 1 --branch z3-4.5.0 https://github.com/Z3Prover/z3 "$BUILDDIR/z3"
pushd "$BUILDDIR/z3"
  python scripts/mk_make.py --ml -p "$BUILDDIR/z3/build"
  pushd build
    # -jN here may break the make (hidden deps or something)
    make
    make install

    # Weird, but required sometimes
    sudo ln -s "$BUILDDIR/z3/build/libz3.so" "/usr/lib/libz3.so"
    sudo ldconfig
  popd
popd


### VeriFast

# directly from VeriFast's readme
sudo apt-get install -y --no-install-recommends \
                     ca-certificates m4 \
                     ocaml-native-compilers gcc camlp4 patch unzip libgtk2.0-dev \
                     valac gtksourceview2.0-dev \
                     liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev

# Not mentioned by VeriFast's readme, required anyway
opam install ocamlfind camlp4 -y

git clone --depth 1 --branch export_path_conditions https://github.com/SolalPirelli/verifast "$BUILDDIR/verifast"
pushd "$BUILDDIR/verifast/src"
  make verifast # should be just "make" but the verifast checks fail due to a non auto lemma
  echo 'PATH=$PATH:'"$BUILDDIR/verifast/bin" >> "$PATHSFILE"
  . "$PATHSFILE"
popd


### KLEE

svn co https://llvm.org/svn/llvm-project/llvm/tags/RELEASE_342/final "$BUILDDIR/llvm"
svn co https://llvm.org/svn/llvm-project/cfe/tags/RELEASE_342/final "$BUILDDIR/llvm/tools/clang"
svn co https://llvm.org/svn/llvm-project/libcxx/tags/RELEASE_342/final "$BUILDDIR/llvm/projects/libcxx"
pushd "$BUILDDIR/llvm"
  CXXFLAGS="-D_GLIBCXX_USE_CXX11_ABI=0" ./configure --enable-optimized --disable-assertions --enable-targets=host --with-python='/usr/bin/python2'
  make -j $(nproc)
  echo 'PATH=$PATH:'"$BUILDDIR/llvm/Release/bin" >> "$PATHSFILE"
  . "$PATHSFILE"
popd

git clone --depth 1 --branch fix_no_buffers https://github.com/SolalPirelli/klee-uclibc.git "$BUILDDIR/klee-uclibc"
pushd "$BUILDDIR/klee-uclibc"
  ./configure \
   --make-llvm-lib \
   --with-llvm-config="../llvm/Release/bin/llvm-config" \
   --with-cc="../llvm/Release/bin/clang"

  # Use our minimalistic config
  cp "$VNDSDIR/install/klee-uclibc.config" '.config'

  make -j $(nproc)
popd

git clone --depth 1 --branch timed-access-dirty-rebased https://github.com/SolalPirelli/klee.git "$BUILDDIR/klee"
pushd "$BUILDDIR/klee"
  mkdir build
  pushd build
    CXXFLAGS="-D_GLIBCXX_USE_CXX11_ABI=0" \
    CMAKE_PREFIX_PATH="$BUILDDIR/z3/build" \
    CMAKE_INCLUDE_PATH="$BUILDDIR/z3/build/include/" \
     cmake \
     -DENABLE_UNIT_TESTS=OFF \
     -DBUILD_SHARED_LIBS=OFF \
     -DENABLE_KLEE_ASSERTS=OFF \
     -DLLVM_CONFIG_BINARY="$BUILDDIR/llvm/Release/bin/llvm-config" \
     -DLLVMCC="$BUILDDIR/llvm/Release/bin/clang" \
     -DLLVMCXX="$BUILDDIR/llvm/Release/bin/clang++" \
     -DENABLE_SOLVER_Z3=ON \
     -DENABLE_KLEE_UCLIBC=ON \
     -DKLEE_UCLIBC_PATH="$BUILDDIR/klee-uclibc" \
     -DENABLE_POSIX_RUNTIME=ON \
     ..
    make -j $(nproc)
    echo 'PATH=$PATH:'"$BUILDDIR/klee/build/bin" >> "$PATHSFILE"
    echo "export KLEE_INCLUDE=$BUILDDIR/klee/include" >> "$PATHSFILE"
    . "$PATHSFILE"
  popd
popd


### DPDK


# On the Linux subsystem for Windows, uname -r includes a "-Microsoft" token
KERNEL_VER=$(uname -r | sed 's/-Microsoft//')

# Install the right headers; we do *not* install headers on Docker since it uses the underlying kernel
if [ "$OS" = 'microsoft' ]; then
  # Fix the kernel dir, since the Linux subsystem for Windows doesn't have an actual Linux kernel...
  sudo apt install "linux-headers-$KERNEL_VER-generic"
  export RTE_KERNELDIR="/usr/src/linux-headers-$KERNEL_VER-generic/"
elif [ "$OS" = 'linux' ]; then
  sudo apt-get install -y "linux-headers-$KERNEL_VER"
fi

pushd "$BUILDDIR"
  wget -O dpdk.tar.xz http://static.dpdk.org/rel/dpdk-16.07.tar.xz
  tar xf dpdk.tar.xz
  rm dpdk.tar.xz
  mv dpdk-16.07 dpdk

  echo 'export RTE_TARGET=x86_64-native-linuxapp-gcc' >> "$PATHSFILE"
  echo "export RTE_SDK=$BUILDDIR/dpdk" >> "$PATHSFILE"
  . "$PATHSFILE"

  pushd dpdk
    # Apply the Vigor patches ( :( )
    patch -p1 < "$VNDSDIR/install/dpdk.patch"
    patch -p1 < "$VNDSDIR/install/dpdk.config.patch"

    make config T=x86_64-native-linuxapp-gcc
    make install -j T=x86_64-native-linuxapp-gcc DESTDIR=.
  popd
popd


### Validator dependencies

opam install ocamlfind core sexplib menhir -y

echo "source $PATHSFILE" >> .profile

