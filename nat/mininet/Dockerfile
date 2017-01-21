FROM ubuntu:14.04
RUN apt-get update && apt-get install -y \
    wget build-essential libpcap-dev \
    linux-headers-3.13.0-35-generic libglib2.0-dev \
    tcpdump && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* && \
    mv /usr/sbin/tcpdump /usr/bin/tcpdump
# ^^ last line -- to overcome the apparmor issue for
# running libcrypto.so in --privileged mode
WORKDIR /root
RUN wget http://dpdk.org/browse/dpdk/snapshot/dpdk-2.2.0.tar.gz -O dpdk.tar.gz && \
    tar xf dpdk.tar.gz && \
    mv dpdk-* dpdk && \
    rm dpdk.tar.gz
WORKDIR /root/dpdk
RUN sed -ri 's,(PMD_PCAP=).*,\1y,' config/common_linuxapp && \
    make config install -j4 T=x86_64-native-linuxapp-gcc
ENV RTE_SDK=/root/dpdk \
    RTE_TARGET=x86_64-native-linuxapp-gcc
LABEL RUN docker run -it --privileged 
RUN mkdir /root/nat
COPY *.h *.c Makefile /root/nat/
COPY containers/ /root/nat/containers/
WORKDIR /root/nat
RUN make
