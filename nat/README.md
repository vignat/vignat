Here you can see the development of a NAT-box, based on the DPDK framework, and verified with Klee.

This directory contains a draft of test-setup for the NAT implemented. (It does not work yet, though). To make use of it, you need to install the recent Docker (1.9) that supports advanced networking. The default package provided is usually outdated. See [this link](https://docs.docker.com/engine/installation/ubuntulinux/) for the oficiall installation guide.

Once you installed it, just try:

```sh
   $ sh test.sh
```

Although, it does not work yet, probably due to the [issue](http://stackoverflow.com/questions/34440097/why-do-ping-packets-not-reach-a-custom-gateway-in-docker) in the Docker networking.

To remove all the generated networks and containers, run

```sh
   $ sh cleanup.sh
```