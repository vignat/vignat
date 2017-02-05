#!/bin/bash

pushd $HOME >> /dev/null
if [ ! -f moon-gen/.built ]; then
    git clone --depth=1 git://github.com/emmericp/MoonGen.git moon-gen

    cd moon-gen
    ./build.sh

    touch .built
fi

popd >> /dev/null
