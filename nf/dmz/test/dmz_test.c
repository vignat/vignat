#include <inttypes.h>

#include <rte_atomic.h>
#include <rte_byteorder.h>
#include <rte_ethdev.h>
#include <rte_ether.h>
#include <rte_ip.h>
#include <rte_mbuf.h>

#include "../../lib/nf_forward.h"
#include "../../lib/nf_util.h"

#include "../dmz_config.h"

// infrastructure
struct rte_mempool* pool;


// time
static uint32_t now = 1;
#define EXP_TIME 10

// zones
#define INTERNET 0
#define DMZ 1
#define INTRANET 2
#define MASK IPv4(255, 255, 255, 0)
#define DMZ_BLOCK IPv4(100, 0, 0, 0)
#define INTRANET_BLOCK IPv4(200, 0, 0, 0)
#define INTERNET_1 IPv4(1, 0, 0, 1)
#define INTERNET_2 IPv4(1, 0, 0, 2)
#define DMZ_1 IPv4(100, 0, 0, 1)
#define DMZ_2 IPv4(100, 0, 0, 2)
#define INTRANET_1 IPv4(200, 0, 0, 1)
#define INTRANET_2 IPv4(200, 0, 0, 2)

char*
zone_name(uint8_t device)
{
	if (device == INTERNET) return "INTERNET";
	if (device == DMZ) return "DMZ";
	return "INTRANET";
}

int
packet(uint32_t src_ip, uint16_t src_port, uint8_t src_device, uint32_t dst_ip, uint16_t dst_port)
{
	struct rte_mbuf* mbuf = rte_pktmbuf_alloc(pool);
	if (mbuf == NULL) {
		rte_exit(EXIT_FAILURE, "Can't allocate a message!");
	}

	struct ether_hdr* ether_header = nf_get_mbuf_ether_header(mbuf);
	ether_header->ether_type = rte_cpu_to_be_16(ETHER_TYPE_IPv4);

	struct ipv4_hdr* ipv4_header = nf_get_mbuf_ipv4_header(mbuf);
	ipv4_header->src_addr = src_ip;
	ipv4_header->dst_addr = dst_ip;
	ipv4_header->next_proto_id = IPPROTO_TCP;

	struct tcpudp_hdr* tcp_header = nf_get_ipv4_tcpudp_header(ipv4_header);
	tcp_header->src_port = src_port;
	tcp_header->dst_port = dst_port;

	int dst_device = nf_core_process(src_device, mbuf, now);

	rte_pktmbuf_free(mbuf);

	return dst_device;
}

void
forwards(char* name, uint32_t src_ip, uint16_t src_port, uint8_t src_device, uint32_t dst_ip, uint16_t dst_port, int dst_device)
{
	int actual_dst_device = packet(src_ip, src_port, src_device, dst_ip, dst_port);

	if (actual_dst_device != dst_device) {
		char* actual_name = actual_dst_device == src_device ? "DROP" : zone_name(actual_dst_device);
		char* expected_name = dst_device == src_device ? "DROP" : zone_name(dst_device);

		printf("ASSERT FAILURE, expected %s but got %s in: %s\n", expected_name, actual_name, name);
	}
}

void
drops(char* name, uint32_t src_ip, uint16_t src_port, uint8_t src_device, uint32_t dst_ip, uint16_t dst_port)
{
	forwards(name, src_ip, src_port, src_device, dst_ip, dst_port, src_device);
}


static struct dmz_config config = {
        .internet_device = INTERNET,
        .dmz_device = DMZ,
        .intranet_device = INTRANET,

        .dmz_block_addr = DMZ_BLOCK,
        .dmz_block_mask = MASK,
        .intranet_block_addr = INTRANET_BLOCK,
        .intranet_block_mask = MASK,

        .expiration_time = EXP_TIME,

        .max_flows = 1024
};


int
main(int argc, char* argv[])
{
	// Initialize the Environment Abstraction Layer (EAL)
	int ret = rte_eal_init(argc, argv);
	if (ret < 0) {
		rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
	}
	printf("Initialized EAL.\n");

	// infrastructure
	pool = rte_pktmbuf_pool_create(
		"MEMPOOL", // name
		8192 * rte_eth_dev_count(), // #elements
		256, // cache size
		0, // application private area size
		RTE_MBUF_DEFAULT_BUF_SIZE, // data buffer size
		rte_socket_id() // socket ID
	);
	if (pool == NULL) {
		rte_exit(EXIT_FAILURE, "Cannot create mbuf pool\n");
	}

	nf_config_set(&config);
	nf_core_init();


	printf("Running tests...\n");

	drops("BAD: Intra IP from DMZ device",
	 /* src: */ INTRANET_1, 0, DMZ,
         /* dst: */ INTERNET_1, 0);
        drops("BAD: Intra IP from Internet device",
         /* src: */ INTRANET_1, 0, INTERNET,
         /* dst: */ DMZ_1, 0);
        drops("BAD: DMZ IP from Intranet device",
         /* src: */ DMZ_1, 0, INTRANET,
         /* dst: */ INTERNET_1, 0);
        drops("BAD: DMZ IP from Internet device",
         /* src: */ DMZ_1, 0, INTERNET,
         /* dst: */ INTRANET_1, 0);
        drops("BAD: Internet IP from Intranet device",
         /* src: */ INTERNET_1, 0, INTRANET,
         /* dst: */ DMZ_1, 0);
        drops("BAD: Internet IP from Intranet device",
         /* src: */ INTERNET_1, 0, DMZ,
         /* dst: */ INTRANET_1, 0);

	drops("BAD: Intra->Intra",
	 /* src: */ INTRANET_1, 0, INTRANET,
	 /* dst: */ INTRANET_2, 0);
	drops("BAD: DMZ->DMZ",
	 /* src: */ DMZ_1, 0, DMZ,
	 /* dst: */ DMZ_2, 0);
	drops("BAD: Inter->Inter",
	 /* src: */ INTERNET_1, 0, INTERNET,
	 /* dst: */ INTERNET_2, 0);


	now = 100;
	forwards("Internet->DMZ",
	 /* src */ INTERNET_1, 0, INTERNET,
	 /* dst */ DMZ_1, 0, DMZ);

	now = 200;
	forwards("DMZ->Internet",
	 /* src */ DMZ_1, 0, DMZ,
	 /* dst */ INTERNET_1, 0, INTERNET);


	now = 300;
	drops("UNAUTHORIZED: Internet->Intranet",
	 /* src */ INTERNET_1, 0, INTERNET,
	 /* dst */ INTRANET_1, 0);

	now = 400;
	drops("UNAUTHORIZED: DMZ->Intranet",
	 /* src */ DMZ_1, 0, DMZ,
	 /* dst */ INTRANET_1, 0);


	now = 500;
	forwards("NEW FLOW: Intranet->Internet",
	 /* src */ INTRANET_1, 0, INTRANET,
	 /* dst */ INTERNET_1, 0, INTERNET);
	forwards("EXISTING FLOW: Internet->Intranet",
	 /* src */ INTERNET_1, 0, INTERNET,
	 /* dst */ INTRANET_1, 0, INTRANET);
	drops("UNAUTHORIZED: Internet->Intranet other flow",
	 /* src */ INTERNET_1, 1, INTERNET,
	 /* dst */ INTRANET_1, 0);
	drops("UNAUTHORIZED: Internet->Intranet other flow",
	 /* src */ INTERNET_2, 0, INTERNET,
	 /* dst */ INTRANET_1, 0);
	drops("UNAUTHORIZED: Internet->Intranet other flow",
	 /* src */ INTERNET_1, 0, INTERNET,
	 /* dst */ INTRANET_1, 1);
	drops("UNAUTHORIZED: Internet->Intranet other flow",
	 /* src */ INTERNET_1, 0, INTERNET,
	 /* dst */ INTRANET_2, 0);

	printf("Done!\n");
}
