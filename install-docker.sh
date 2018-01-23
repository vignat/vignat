#!/bin/bash
# Creates an image with the Vigor container if it doesn't already exists, and launches a container

# Bash "strict mode"
set -euxo pipefail


VNDSDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
KERNEL_VER=$(uname -r | sed 's/-generic//')
IMAGE_NAME='vigor'


# Make sure we have the Linux headers
sudo apt-get install -y "linux-headers-$KERNEL_VER"


# Create the image if needed
if [ -z "$(sudo docker images -q $IMAGE_NAME)" ]; then
  # HACK: Docker doesn't support absolute paths in COPY
  #       so we create symlinks instead...
  #       ...except Docker doesn't like that either,
  #       so we use mount points...
  mkdir usr
  sudo mount --bind /usr usr
  mkdir lib
  sudo mount --bind /lib lib

  sudo docker build "$VNDSDIR" --build-arg "kernel_ver=$KERNEL_VER" -t "$IMAGE_NAME"

  #       ... and then delete them
  sudo umount usr
  rmdir usr
  sudo umount lib
  rmdir lib
fi

# Run the container
sudo docker run -i -t "$IMAGE_NAME"
