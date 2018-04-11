# Minimize image size using a small base
FROM ubuntu:xenial

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
COPY .travis/install-generic.sh /home/vigor/install-generic.sh
COPY .travis/install-dpdk.sh /home/vigor/install-dpdk.sh
COPY .travis/install-all.sh /home/vigor/install-all.sh
RUN /home/vigor/install-all.sh

# Pass -l to bash so it reads ~/.profile
ENTRYPOINT ["/bin/bash", "-l"]
