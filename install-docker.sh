#!/bin/bash
# Creates an image with the Vigor container if it doesn't already exists, and launches a container

# Bash "strict mode"
set -euxo pipefail


VNDSDIR=$(cd $(dirname "${BASH_SOURCE[0]}") && pwd)
KERNEL_VER="$(uname -r)"
HEADERS_PATH="/usr/src/linux-headers-$KERNEL_VER"
IMAGE_NAME='vigor'

# Make sure we have the Linux headers
sudo apt-get install -y "linux-headers-$KERNEL_VER"

# Create the image if needed
if [ -z "$(sudo docker images -q $IMAGE_NAME)" ]; then
  sudo docker build "$VNDSDIR" -t "$IMAGE_NAME"
fi

sudo docker run -v "$HEADERS_PATH:$HEADERS_PATH" -i -t "$IMAGE_NAME"
