#include <klee/klee.h>
#include <string.h>
#include "rte_stubs.h"
#include "../flow.h"

int rte_errno;

uint64_t rte_get_tsc_hz(){
    return 0;
}

unsigned rte_lcore_id(){
    return 0;
}

uint64_t rte_rdtsc(){
  //TODO: this prevents the simulation of sending leftover packets, (or all?)
  return 0;
}

struct str_field_descr mbuf_descrs[] = {
  //Do not forget about "buf_addr" -- it is a pointer that is why it is not listed here.
  {offsetof(struct rte_mbuf, buf_physaddr), sizeof(uint64_t), "buf_physaddr"},
  {offsetof(struct rte_mbuf, buf_len), sizeof(uint16_t), "buf_len"},
  {offsetof(struct rte_mbuf, data_off), sizeof(uint16_t), "data_off"},
  {offsetof(struct rte_mbuf, refcnt), sizeof(uint16_t), "refcnt"},
  {offsetof(struct rte_mbuf, nb_segs), sizeof(uint8_t), "nb_segs"},
  {offsetof(struct rte_mbuf, port), sizeof(uint8_t), "port"},
  {offsetof(struct rte_mbuf, ol_flags), sizeof(uint64_t), "ol_flags"},
  {offsetof(struct rte_mbuf, packet_type), sizeof(uint32_t), "packet_type"},
  {offsetof(struct rte_mbuf, pkt_len), sizeof(uint32_t), "pkt_len"},
  {offsetof(struct rte_mbuf, data_len), sizeof(uint16_t), "data_len"},
  {offsetof(struct rte_mbuf, vlan_tci), sizeof(uint16_t), "vlan_tci"},
  {offsetof(struct rte_mbuf, hash), sizeof(uint32_t), "hash"},
  {offsetof(struct rte_mbuf, seqn), sizeof(uint32_t), "seqn"},
  {offsetof(struct rte_mbuf, vlan_tci_outer), sizeof(uint16_t), "vlan_tci_outer"},
  {offsetof(struct rte_mbuf, udata64), sizeof(uint64_t), "udata64"},
  {offsetof(struct rte_mbuf, pool), sizeof(void*), "pool"},
  {offsetof(struct rte_mbuf, next), sizeof(struct rte_mbuf*), "next"},
  {offsetof(struct rte_mbuf, tx_offload), sizeof(uint64_t), "tx_offload"},
  {offsetof(struct rte_mbuf, priv_size), sizeof(uint16_t), "priv_size"},
  {offsetof(struct rte_mbuf, timesync), sizeof(uint16_t), "timesync"},
};

struct nested_field_descr user_buf_nested[] = {
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, ether_type), sizeof(uint16_t), "ether_type"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, d_addr), sizeof(struct ether_addr), "d_addr"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, s_addr), sizeof(struct ether_addr), "s_addr"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, version_ihl), sizeof(uint8_t), "version_ihl"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, type_of_service), sizeof(uint8_t), "type_of_service"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, total_length), sizeof(uint16_t), "total_length"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, packet_id), sizeof(uint16_t), "packet_id"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, fragment_offset), sizeof(uint16_t), "fragment_offset"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, time_to_live), sizeof(uint8_t), "time_to_live"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, next_proto_id), sizeof(uint8_t), "next_proto_id"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, hdr_checksum),
    sizeof(uint16_t), "hdr_checksum"},
  */
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, src_addr), sizeof(uint32_t), "src_addr"},
  {offsetof(struct user_buf, ipv4), offsetof(struct ipv4_hdr, dst_addr), sizeof(uint32_t), "dst_addr"},

  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, sent_seq), sizeof(uint32_t), "sent_seq"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, recv_ack), sizeof(uint32_t), "recv_ack"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, data_off), sizeof(uint8_t), "data_off"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, tcp_flags), sizeof(uint8_t), "tcp_flags"},
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, rx_win), sizeof(uint16_t), "rx_win"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, cksum),
    sizeof(uint16_t), "cksum"},
  */
  {offsetof(struct user_buf, tcp), offsetof(struct tcp_hdr, tcp_urp), sizeof(uint16_t), "tcp_urp"},
};

struct nested_nested_field_descr user_buf_n2[] = {
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, d_addr), 0, sizeof(uint8_t), "a"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, d_addr), 1, sizeof(uint8_t), "b"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, d_addr), 2, sizeof(uint8_t), "c"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, d_addr), 3, sizeof(uint8_t), "d"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, d_addr), 4, sizeof(uint8_t), "e"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, d_addr), 5, sizeof(uint8_t), "f"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, s_addr), 0, sizeof(uint8_t), "a"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, s_addr), 1, sizeof(uint8_t), "b"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, s_addr), 2, sizeof(uint8_t), "c"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, s_addr), 3, sizeof(uint8_t), "d"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, s_addr), 4, sizeof(uint8_t), "e"},
  {offsetof(struct user_buf, ether), offsetof(struct ether_hdr, s_addr), 5, sizeof(uint8_t), "f"},
};

#define KLEE_TRACE_USER_BUF(u_ptr)                            \
  klee_trace_extra_ptr(u_ptr, sizeof(struct user_buf),                  \
                       "user_buf_addr", "");                            \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct user_buf, ether),   \
                             sizeof(struct ether_hdr), "ether");        \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct user_buf, ipv4),    \
                             sizeof(struct ipv4_hdr), "ipv4");          \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct user_buf, tcp),     \
                             sizeof(struct tcp_hdr), "tcp");            \
  for (int i = 0; i < sizeof(user_buf_nested)/sizeof(user_buf_nested[0]); ++i) {\
    klee_trace_extra_ptr_nested_field(u_ptr,                  \
                                      user_buf_nested[i].base_offset,   \
                                      user_buf_nested[i].offset,        \
                                      user_buf_nested[i].width,         \
                                      user_buf_nested[i].name);         \
  }                                                                     \
  for (int i = 0; i < sizeof(user_buf_n2)/sizeof(user_buf_n2[0]); ++i) { \
    klee_trace_extra_ptr_nested_nested_field                            \
      (u_ptr,                                                 \
       user_buf_n2[i].base_base_offset,                                 \
       user_buf_n2[i].base_offset,                                      \
       user_buf_n2[i].offset,                                           \
       user_buf_n2[i].width,                                            \
       user_buf_n2[i].name);                                            \
  }

#define KLEE_TRACE_MBUF(m_ptr, dir)                                     \
  klee_trace_param_ptr_directed(m_ptr, sizeof(*m_ptr), #m_ptr, dir);        \
  klee_trace_param_ptr_field_directed(m_ptr, offsetof(struct rte_mbuf, buf_addr), \
                                      sizeof(struct user_buf*), "buf_addr", \
                                      dir);                             \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) { \
    klee_trace_param_ptr_field_directed(m_ptr,                          \
                                        mbuf_descrs[i].offset,          \
                                        mbuf_descrs[i].width,           \
                                        mbuf_descrs[i].name,            \
                                        dir);                           \
  }

#define KLEE_TRACE_MBUF_EPTR(m_ptr, pname)                               \
  klee_trace_extra_ptr(m_ptr, sizeof(*m_ptr), pname, "");                \
  klee_trace_extra_ptr_field(m_ptr, offsetof(struct rte_mbuf, buf_addr), \
                             sizeof(struct user_buf*), "buf_addr");     \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) { \
    klee_trace_extra_ptr_field(m_ptr,                                   \
                               mbuf_descrs[i].offset,                   \
                               mbuf_descrs[i].width,                    \
                               mbuf_descrs[i].name);                    \
  }

// " <-- work around a bug in nano with string syntax coloring caused by the macro above

struct user_buf user_buf;

struct rte_mbuf incoming_package; //for two ports
int incoming_package_allocated;

static void
received_packet(uint8_t device, struct rte_mbuf** mbuf)
{
	klee_trace_ret();
	klee_trace_param_i32(device, "received_packet_device");
  klee_trace_param_ptr(mbuf, sizeof(struct rte_mbuf*), "mbuf");
	KLEE_TRACE_MBUF_EPTR(&incoming_package, "incoming_package");
  KLEE_TRACE_USER_BUF(&user_buf);

  klee_allow_access(&user_buf, sizeof(struct user_buf));
  klee_allow_access(&incoming_package, sizeof(struct rte_mbuf));
  klee_assert(!incoming_package_allocated);
  *mbuf = &incoming_package;
  incoming_package_allocated = 1;
}

void init_symbolic_user_buf() {
  void* array = malloc(sizeof(struct user_buf));
  klee_make_symbolic(array, sizeof(struct user_buf), "user_buf");
  memcpy(&user_buf, array, sizeof(struct user_buf));
  user_buf.ipv4.total_length =
    rte_cpu_to_be_16(sizeof(struct ipv4_hdr) + sizeof(struct tcp_hdr));
}

void init_symbolic_inc_pkt() {
  void* array = malloc(sizeof(struct rte_mbuf));
  klee_make_symbolic(array, sizeof(struct rte_mbuf), "incoming_package");
  memcpy(&incoming_package, array, sizeof(struct rte_mbuf));
  incoming_package.buf_addr = &user_buf;
  incoming_package.data_off = 0;// TODO: symbolic
  /* (*mbuf)->port = device; */
  /* (*mbuf)->userdata = NULL; */
  /* (*mbuf)->pool = NULL; */
  /* (*mbuf)->next = NULL; */
  /* (*mbuf)->pkt_len = sizeof(struct user_buf); */
  /* (*mbuf)->data_len = 0; // what is the correct value??? */
}

uint16_t rte_eth_rx_burst(uint8_t portid, uint8_t queueid,
                          struct rte_mbuf** pkts_burst, int max_burst){
  klee_assert(portid < RTE_MAX_ETHPORTS);
  int receive_one;
  klee_make_symbolic(&receive_one, sizeof(int), "receive_one");
  if (receive_one) {
    received_packet(portid, &pkts_burst[0]);
    return 1;
  } else {
    return 0;
  }
}

void rte_pktmbuf_free(struct rte_mbuf *mbufp){
  klee_trace_ret();
  KLEE_TRACE_MBUF(mbufp, TD_IN);
  KLEE_TRACE_USER_BUF(mbufp->buf_addr);
  klee_forbid_access(mbufp->buf_addr,
                     sizeof(struct user_buf),
                     "pkt freed");
  klee_forbid_access(mbufp, sizeof(struct rte_mbuf),
                     "pkt freed");
  return;
}

static int
send_single_packet(struct rte_mbuf *m, uint8_t port)
{
  klee_trace_ret();
  KLEE_TRACE_MBUF(m, TD_IN);
  KLEE_TRACE_USER_BUF(m->buf_addr);
  klee_trace_param_i32(port, "portid");
  int packet_sent = klee_int("packet_sent");
  if (packet_sent) {
    klee_forbid_access(m->buf_addr, sizeof(struct user_buf),
                       "pkt sent");
    klee_forbid_access(m, sizeof(struct rte_mbuf), "pkt sent");
  }
  return packet_sent;
}

uint16_t rte_eth_tx_burst(uint8_t port, uint16_t queueid,
                          struct rte_mbuf **tx_pkts, uint16_t n){
  int packet_sent = send_single_packet(tx_pkts[0], port);
  if (packet_sent) return 1;
  else return 0;
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

unsigned rte_socket_id(void){
  return 0;
}

unsigned rte_eth_dev_socket_id(uint8_t device){
  return 0;
}

void rte_eth_link_get_nowait(uint8_t portid, struct rte_eth_link* link){
    return;
}

void rte_delay_ms(unsigned ms){
    return;
}

int rte_eal_init(int argc, char ** argv){
  init_symbolic_user_buf();
  init_symbolic_inc_pkt();
  klee_forbid_access(&user_buf,
                     sizeof(struct user_buf),
                     "pkt is yet to be received");
  klee_forbid_access(&incoming_package,
                     sizeof(struct rte_mbuf),
                     "pkt is yet to be received");
  return 0;
}

uint8_t rte_eth_dev_count(){
  return 2;//FIXME: return symbolic
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

struct rte_mempool default_pools[5];
int last_pool_alloc = -1;

struct rte_mempool *
rte_pktmbuf_pool_create(const char *name, unsigned n,
                        unsigned cache_size, uint16_t priv_size,
                        uint16_t data_room_size,
                        int socket_id){
  klee_assert(last_pool_alloc < 5);
  ++last_pool_alloc;
  strncpy(default_pools[last_pool_alloc].name,
          name, RTE_MEMPOOL_NAMESIZE);
  default_pools[last_pool_alloc] = (struct rte_mempool){
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

  return &default_pools[last_pool_alloc];
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

const char* rte_strerror(int errnum) {
  return "rte_strerror stub. no help here";
}

struct rte_mbuf* rte_pktmbuf_clone(struct rte_mbuf *md,
                                   struct rte_mempool *mp) {
  printf("rte_pktmbuf_clone is not implemented");
  return NULL;
}

void flood(struct rte_mbuf* frame,
           uint8_t skip_device,
           uint8_t nb_devices) {
  klee_trace_ret();
  KLEE_TRACE_MBUF(frame, TD_IN);
  KLEE_TRACE_USER_BUF(frame->buf_addr);
  klee_trace_param_i32(skip_device, "skip_device");
  klee_trace_param_i32(nb_devices, "nb_devices");
  klee_forbid_access(frame->buf_addr, sizeof(struct user_buf),
                     "pkt flooded");
  klee_forbid_access(frame,
                     sizeof(struct rte_mbuf),
                     "pkt flooded");
}
