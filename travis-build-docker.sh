sudo docker build . -f travis.dockerfile --build-arg "kernel_ver=$(uname -r | sed 's/-generic//')" -t vigor.travis
