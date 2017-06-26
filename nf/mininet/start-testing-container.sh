#!/bin/bash
# Set up and start a testing container for checking the development of klee
# verification of the NAT box.

CONTAINER_NAME=testver
KLEE_ROOT=~/klee
VNDS_ROOT=~/vnds

while [[ $# > 1 ]]
do
    key="$1"
    case $key in
        -n|--name)
            CONTAINER_NAME="$2"
            shift
            ;;
        -k|--klee)
            KLEE_ROOT="$2"
            shift
            ;;
        -v|--vnds)
            VNDS_ROOT="$2"
            shift
            ;;
        *)
            echo "unknown argument $key"
            ;;
    esac
    shift
done

USER_ID=`id -u`
USER_NAME=`id -u -n`
GROUP_ID=`id -g`
GROUP_NAME=`id -g -n`

if [[ "$(docker images -q ver 2> /dev/null)" == "" ]]; then
    docker build --tag=ver --file=verification.docker .
fi

docker run -itd -e USER_ID=$USER_ID -e USER_NAME=$USER_NAME \
       -e GROUP_NAME=$GROUP_NAME -e GROUP_ID=$GROUP_ID --name $CONTAINER_NAME \
       -v $KLEE_ROOT:/work/klee -v $VNDS_ROOT/nat:/work/nat \
       -v $PWD/testing-container-initializer.sh:/root/.bashrc ver bash

