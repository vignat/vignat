# This script is intented to be run inside of the docker container.
# It expects the following environment variables to be passed when
# the container started: USER_ID, USER_NAME, GROUP_ID, GROUP_NAME.
# it first changes the user to match the host user, then chowns
# development files to the newly created user, and passes control.

groupadd -f --gid $GROUP_ID $GROUP_NAME
useradd --uid $USER_ID --gid $GROUP_ID --groups sudo $USER_NAME
chown -Rf $USER_NAME:$GROUP_NAME /work/klee-uclibc /work/dpdk /work/stp /work/minisat
chown $USER_NAME:$GROUP_NAME /work

echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers

cd /work
sed -ri "s|(ENV_PATH\s*PATH=).*|\1$PATH|" /etc/login.defs
export HOME=/work
su -m $USER_NAME -

