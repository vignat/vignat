#!/bin/bash
# Tested on Ubuntu 16.04, Debian Stretch, and the Linux Subsystem for Windows
# $1: "dpdk-only" to only install DPDK, or no argument to install everything

# Setup

VNDSDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
BUILDDIR=`pwd`
PATHSFILE="$BUILDDIR/paths.sh"

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

echo "install mode: $VIGOR_INSTALL_MODE"

if [ "$BUILDDIR" -ef "$VNDSDIR" ] && [ "$OS" != "docker" ] && [ "$VIGOR_INSTALL_MODE" != "travis" ] ; then
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

echo '# The configuration paths for VNDS dependencies' > "$PATHSFILE"

# Source the paths file at login
echo ". $PATHSFILE" >> "$HOME/.profile"


### DPDK initialization
sudo apt-get update

sudo apt-get install -y \
                     libpcap-dev libnuma-dev `# for DPDK` \
                     wget build-essential git python `# for more or less everything`

# On the Linux subsystem for Windows, uname -r includes a "-Microsoft" token
KERNEL_VER=$(uname -r | sed 's/-Microsoft//')

# Install the right headers; we do *not* install headers on Docker since it uses the underlying kernel
if [ "$OS" = 'microsoft' ]; then
  # Fix the kernel dir, since the Linux subsystem for Windows doesn't have an actual Linux kernel...
  sudo apt install "linux-headers-$KERNEL_VER-generic"
  export RTE_KERNELDIR="/usr/src/linux-headers-$KERNEL_VER-generic/"
elif [ "$OS" = 'linux' ] || [ "$VIGOR_INSTALL_MODE" = "travis" ] ; then
  sudo apt-get install -y "linux-headers-$KERNEL_VER"
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


if [ $# -ne 0 ] && [ "$1" = "dpdk-only" ]; then
  echo "dpdk-only flag given, not installing other stuff"
  exit 0
fi


### Non-DPDK initialization

sudo apt-get install -y \
                     time `# to measure verification time` \
                     bison flex zlib1g-dev libncurses5-dev libcap-dev cmake subversion `# for KLEE/LLVM` \
                     parallel `# for the Vigor Validator` \
                     opam m4 `# for OCaml; m4 is not a dependency in theory but it is in practice` \

# for VeriFast
# directly from VeriFast's readme
sudo apt-get install -y --no-install-recommends \
                     ca-certificates m4 \
                     ocaml-native-compilers gcc camlp4 patch unzip libgtk2.0-dev \
                     valac gtksourceview2.0-dev \
                     liblablgtk2-ocaml-dev liblablgtksourceview2-ocaml-dev

# OCaml uses variables in its scripts without defining it first - we're in strict mode!
if [ -z ${PERL5LIB+x} ]; then
  export PERL5LIB=''
fi
if [ -z ${MANPATH+x} ]; then
  export MANPATH=''
fi

opam init -y
opam switch 4.06.0
echo 'PATH='"$HOME/.opam/system/bin"':$PATH' >> "$PATHSFILE"
echo ". $HOME/.opam/opam-init/init.sh" >> "$PATHSFILE"
. "$PATHSFILE"

# For Z3 ml bindings
# VeriFast requires Z3 in ocamlfind; install it now so that it puts itself in ocamlfind
# Num is required for Big_int
opam install ocamlfind num -y

# for VeriFast
# Not mentioned by VeriFast's readme, required anyway
opam install ocamlfind camlp4 -y

### Validator dependencies
opam install ocamlfind core sexplib menhir -y


### Z3 v4.5

git clone --depth 1 --branch z3-4.5.0 https://github.com/Z3Prover/z3 "$BUILDDIR/z3"
pushd "$BUILDDIR/z3"
  python scripts/mk_make.py --ml -p "$BUILDDIR/z3/build"
  pushd build
    make -k -j $(nproc) || true
    # -jN here may break the make (hidden deps or something)
    make
    make install

    # Weird, but required sometimes TODO: do it only when required
    # TODO find a way to bring it up together with other sudo lines
      # Remove the outdated libz3.so
      sudo apt-get remove libz3-dev || true
      sudo rm -f /usr/lib/x86_64-linux-gnu/libz3.so || true
      sudo rm -f /usr/lib/x86_64-linux-gnu/libz3.so.4 || true
      sudo rm -f /usr/lib/libz3.so || true
      # Install the new libz3.so
      sudo ln -s "$BUILDDIR/z3/build/libz3.so" "/usr/lib/libz3.so"
      sudo ldconfig
  popd
popd


### VeriFast

git clone --depth 1 --branch export_path_conditions https://github.com/vignat/verifast "$BUILDDIR/verifast"
pushd "$BUILDDIR/verifast/src"
  make verifast # should be just "make" but the verifast checks fail due to a non auto lemma
  echo 'PATH='"$BUILDDIR/verifast/bin"':$PATH' >> "$PATHSFILE"
  . "$PATHSFILE"
popd


### KLEE

svn co https://llvm.org/svn/llvm-project/llvm/tags/RELEASE_342/final "$BUILDDIR/llvm"
svn co https://llvm.org/svn/llvm-project/cfe/tags/RELEASE_342/final "$BUILDDIR/llvm/tools/clang"
svn co https://llvm.org/svn/llvm-project/libcxx/tags/RELEASE_342/final "$BUILDDIR/llvm/projects/libcxx"
pushd "$BUILDDIR/llvm"
  CXXFLAGS="-D_GLIBCXX_USE_CXX11_ABI=0" ./configure --enable-optimized --disable-assertions --enable-targets=host --with-python='/usr/bin/python2'
  make -j $(nproc)
  echo 'PATH='"$BUILDDIR/llvm/Release/bin"':$PATH' >> "$PATHSFILE"
  . "$PATHSFILE"
popd

git clone --depth 1 --branch fix_no_buffers https://github.com/vignat/klee-uclibc.git "$BUILDDIR/klee-uclibc"
pushd "$BUILDDIR/klee-uclibc"
  ./configure \
   --make-llvm-lib \
   --with-llvm-config="../llvm/Release/bin/llvm-config" \
   --with-cc="../llvm/Release/bin/clang"

  # Use our minimalistic config
  cp "$VNDSDIR/install/klee-uclibc.config" '.config'

  make -j $(nproc)
popd

git clone --depth 1 --branch timed-access-dirty-rebased https://github.com/vignat/klee.git "$BUILDDIR/klee"
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
    echo 'PATH='"$BUILDDIR/klee/build/bin"':$PATH' >> "$PATHSFILE"
    echo "export KLEE_INCLUDE=$BUILDDIR/klee/include" >> "$PATHSFILE"
    . "$PATHSFILE"
  popd
popd
