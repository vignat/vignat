KERNEL_VER=$(uname -r | sed 's/-generic//')
docker build . -f .travis/travis.dockerfile --build-arg "host_kernel_ver=$KERNEL_VER" -t vigor.travis2
