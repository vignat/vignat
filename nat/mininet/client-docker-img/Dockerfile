FROM ubuntu:14.04
RUN apt-get update && apt-get install -y \
    hping3 tcpdump && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*
CMD tcpdump -i eth0