# Minimize image size using a small base
FROM debian:stretch-slim

# The install script requires sudo
RUN apt-get update && apt-get install -y sudo

# Create (-m == with a homedir) and use an user with passwordless sudo
RUN useradd -m vigor \
 && echo "vigor:vigor" | chpasswd \
 && echo 'vigor ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER vigor
WORKDIR /home/vigor

# Get and execute the install script (with --force to bypass the directory check)
COPY klee-uclibc.config /home/vigor/klee-uclibc.config
COPY install-generic.sh /home/vigor/install-generic.sh
RUN /home/vigor/install-generic.sh --force
COPY install-dpdk.sh /home/vigor/install-dpdk.sh
RUN /home/vigor/install-dpdk.sh

### TODO:VVV
# # Get the NFs and validator
# COPY nf /home/vigor/nf
# COPY validator /home/vigor/validator

# # Give the right permissions
# RUN sudo chown -R vigor:vigor nf \
#  && sudo chown -R vigor:vigor validator

# # Clean up
# RUN sudo rm -rf install \
#  && sudo rm -f install.sh

# Pass -l to bash so it reads ~/.profile
ENTRYPOINT ["/bin/bash", "-l"]
