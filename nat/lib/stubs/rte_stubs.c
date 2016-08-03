#include <klee/klee.h>
#include <string.h>
#include "rte_stubs.h"


uint16_t rte_eth_tx_burst(uint8_t port, uint16_t queueid, struct rte_mbuf **tx_pkts, uint16_t n){
    return 0;
}

void rte_pktmbuf_free(struct rte_mbuf *mbufp){
    return;
}

uint64_t rte_get_tsc_hz(){
    return 0;
}

unsigned rte_lcore_id(){
    return 0;
}

uint64_t rte_rdtsc(){
    return 0;
}

struct user_buf {
    //uint8_t some_data[100];
    struct ether_hdr ether;
    struct ipv4_hdr ipv4;
    struct tcp_hdr tcp;
} user_buf;

struct rte_mbuf incoming_package; //for two ports
int incoming_package_allocated;

uint16_t rte_eth_rx_burst(uint8_t portid, uint8_t queueid,
                          struct rte_mbuf** pkts_burst, int max_burst){
  klee_assert(portid < RTE_MAX_ETHPORTS);
  int receive_one;
  klee_make_symbolic(&receive_one, sizeof(int), "receive_one");
  if (receive_one) {
    struct rte_mbuf * in_package;
    klee_assert(!incoming_package_allocated);
    klee_make_symbolic(&incoming_package, sizeof(struct rte_mbuf), "incoming_package0");
    klee_make_symbolic(&user_buf, sizeof(struct user_buf), "user_buf0");
    in_package = &incoming_package;
    incoming_package_allocated = 1;
    in_package->buf_addr = &user_buf;
    in_package->data_off = 0;//100;
    in_package->port = portid;
    in_package->userdata = NULL;
    in_package->pool = NULL;
    in_package->next = NULL;
    in_package->pkt_len = sizeof(struct user_buf);
    in_package->data_len = 0; // what is the right value???
    user_buf.ipv4.total_length = rte_cpu_to_be_16(sizeof(struct ipv4_hdr) + sizeof(struct tcp_hdr));
    pkts_burst[0] = in_package;
    return 1;
  } else {
    return 0;
  }
}

void rte_prefetch0(const volatile void *p){
    return;
}

int rte_lcore_is_enabled(unsigned lcore_id){
    return lcore_id < 1;
}

unsigned rte_lcore_to_socket_id(unsigned lcore_id){
    return 0;
}

void rte_eth_link_get_nowait(uint8_t portid, struct rte_eth_link* link){
    return;
}

void rte_delay_ms(unsigned ms){
    return;
}

int rte_eal_init(int argc, char ** argv){
    return 0;
}

uint8_t rte_eth_dev_count(){
    return 2;
}

uint8_t rte_lcore_count(){
    return 1;
}

int rte_eth_dev_configure(uint8_t portid, uint16_t nb_rx_queue, uint16_t nb_tx_queue, struct rte_eth_conf * port_conf){
    return 0;
}

void rte_eth_macaddr_get(uint8_t portid, struct ether_addr *addr){
    return;
}

void rte_eth_dev_info_get(uint8_t portid, struct rte_eth_dev_info *info){
    return;
}

int rte_eth_tx_queue_setup(uint8_t portid, uint16_t queueid, uint16_t nb_tx_desc, unsigned int socketid, struct rte_eth_txconf* txconf){
    return 0;
}

int rte_eth_rx_queue_setup(uint8_t portid, uint16_t queueid, uint16_t nb_rxd, unsigned int socketid, struct rte_eth_rxconf *rxconf, struct rte_mempool *mpool){
    return 0;
}

int rte_eth_dev_start(uint8_t portid){
    return 0;
}

void rte_eth_promiscuous_enable(uint8_t portid){
    return;
}

int rte_eal_mp_remote_launch(lcore_function_t *f, void* arg,
                             enum rte_rmt_call_master_t call_master){
    
    return f(arg);
}

int rte_eal_wait_lcore(unsigned lcore_id){
    return 0;
}

struct rte_mempool default_pool;
int default_pool_allocated = 0;

struct rte_mempool *
rte_pktmbuf_pool_create(const char *name, unsigned n,
                        unsigned cache_size, uint16_t priv_size, uint16_t data_room_size,
                        int socket_id){
    klee_assert(!default_pool_allocated);
    strncpy(default_pool.name, name, RTE_MEMPOOL_NAMESIZE);
    default_pool = (struct rte_mempool){
	.ring = NULL,
	.phys_addr = 0,
	.flags = 0,
	.size = 0,
	.cache_size = cache_size,
	.cache_flushthresh = 0,
	.elt_size = 0,
        .header_size = 0,
	.trailer_size = 0,
	.private_data_size = 0,
	.pg_num = 0,
	.pg_shift = 0,
	.pg_mask = 0,
	.elt_va_start = 0,
        .elt_va_end = 0,
	//.elt_pa = {};
    };

    default_pool_allocated = 1;
    return &default_pool;
}

unsigned rte_get_master_lcore(){
    return 0;
}

void rte_exit(int exit_code, const char *format, ...)
{
    printf("something went wrong(%s)?\n", format);
    exit(exit_code);
}

void rte_reset()
{
  incoming_package_allocated = 0;
}
