# Minimize image size using a small base
FROM debian:stretch-slim

# Linux version (WITHOUT the -generic)
ARG kernel_ver

# Get the kernel stuff (since Docker shares the kernel with the host)
COPY /usr/src/linux-headers-${kernel_ver} /usr/src/linux-headers-${kernel_ver}
COPY /usr/src/linux-headers-${kernel_ver}-generic /usr/src/linux-headers-${kernel_ver}-generic
COPY /lib/modules/${kernel_ver}-generic /lib/modules/${kernel_ver}-generic

# The install script requires sudo
RUN apt-get update && apt-get install -y sudo

# Create (-m == with a homedir) and use an user with passwordless sudo
RUN useradd -m vigor \
 && echo "vigor:vigor" | chpasswd \
 && echo 'vigor ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER vigor
WORKDIR /home/vigor

# Get and execute the install script (with --force to bypass the directory check)
COPY install /home/vigor/install
COPY install.sh /home/vigor/install.sh
RUN /home/vigor/install.sh --force

# Get the NFs and validator
COPY nf /home/vigor/nf
COPY validator /home/vigor/validator

# Give the right permissions
RUN sudo chown -R vigor:vigor nf \
 && sudo chown -R vigor:vigor validator

# Clean up
RUN sudo rm -rf install \
 && sudo rm -f install.sh

# Pass -l to bash so it reads ~/.profile
ENTRYPOINT ["/bin/bash", "-l"]
