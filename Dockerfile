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
COPY install /home/vigor/install
COPY install.sh /home/vigor/install.sh
RUN /home/vigor/install.sh --force

# Get the NFs and validator
COPY nf /home/vigor/nf
COPY validator /home/vigor/validator
