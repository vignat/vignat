# Bash "strict mode"
set -euxo pipefail

bash /home/vigor/install.sh $@
sudo rm -rf /var/lib/apt/lists/*
#cd /home/vigor/llvm && make clean || true
#cd /home/vigor/dpdk && make clean || true
