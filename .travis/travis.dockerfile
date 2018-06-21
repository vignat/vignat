# Minimize image size using a small base
FROM ubuntu:xenial

ARG host_kernel_ver
ENV HOST_KERNEL_VER=$host_kernel_ver

# The install script requires sudo
RUN apt-get update && apt-get install -y sudo && rm -rf /var/lib/apt/lists/*

# Create (-m == with a homedir) and use an user with passwordless sudo
RUN useradd -m vigor \
 && echo "vigor:vigor" | chpasswd \
 && echo 'vigor ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER vigor
WORKDIR /home/vigor

# Get and execute the install script (with --force to bypass the directory check)
COPY install /home/vigor/install
COPY install.sh /home/vigor/install.sh
COPY .travis/install-clean.sh /home/vigor/install-clean.sh
RUN bash /home/vigor/install-clean.sh

# Pass -l to bash so it reads ~/.profile
ENTRYPOINT ["/bin/bash", "-l"]
