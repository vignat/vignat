// Inspired from the DPDK null driver

#include <device_stub.h>

#include <klee/klee.h>

#include <containers/str-descr.h>

#include <rte_byteorder.h>
#include <rte_dev.h>
#include <rte_ethdev.h>
#include <rte_mbuf.h>

static const char* stub_name = "stub";
static struct ether_addr stub_addr = { .addr_bytes = {0} };
static struct rte_eth_link stub_link = {
	.link_speed = ETH_SPEED_NUM_10G,
	.link_duplex = ETH_LINK_FULL_DUPLEX,
	.link_status = ETH_LINK_DOWN,
	.link_autoneg = ETH_LINK_SPEED_AUTONEG,
};

// BEGIN TRACING
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
struct nested_field_descr stub_mbuf_content_nested[] = {
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, ether_type), sizeof(uint16_t), "ether_type"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), sizeof(struct ether_addr), "d_addr"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), sizeof(struct ether_addr), "s_addr"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, version_ihl), sizeof(uint8_t), "version_ihl"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, type_of_service), sizeof(uint8_t), "type_of_service"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, total_length), sizeof(uint16_t), "total_length"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, packet_id), sizeof(uint16_t), "packet_id"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, fragment_offset), sizeof(uint16_t), "fragment_offset"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, time_to_live), sizeof(uint8_t), "time_to_live"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, next_proto_id), sizeof(uint8_t), "next_proto_id"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, hdr_checksum),
    sizeof(uint16_t), "hdr_checksum"},
  */
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, src_addr), sizeof(uint32_t), "src_addr"},
  {offsetof(struct stub_mbuf_content, ipv4), offsetof(struct ipv4_hdr, dst_addr), sizeof(uint32_t), "dst_addr"},

  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, src_port), sizeof(uint16_t), "src_port"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, dst_port), sizeof(uint16_t), "dst_port"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, sent_seq), sizeof(uint32_t), "sent_seq"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, recv_ack), sizeof(uint32_t), "recv_ack"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, data_off), sizeof(uint8_t), "data_off"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, tcp_flags), sizeof(uint8_t), "tcp_flags"},
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, rx_win), sizeof(uint16_t), "rx_win"},
  /*
    skip the checksum, as it is very hard to verify symbolically.
    {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, cksum),
    sizeof(uint16_t), "cksum"},
  */
  {offsetof(struct stub_mbuf_content, tcp), offsetof(struct tcp_hdr, tcp_urp), sizeof(uint16_t), "tcp_urp"},
};
struct nested_nested_field_descr stub_mbuf_content_n2[] = {
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 0, sizeof(uint8_t), "a"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 1, sizeof(uint8_t), "b"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 2, sizeof(uint8_t), "c"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 3, sizeof(uint8_t), "d"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 4, sizeof(uint8_t), "e"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, d_addr), 5, sizeof(uint8_t), "f"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 0, sizeof(uint8_t), "a"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 1, sizeof(uint8_t), "b"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 2, sizeof(uint8_t), "c"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 3, sizeof(uint8_t), "d"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 4, sizeof(uint8_t), "e"},
  {offsetof(struct stub_mbuf_content, ether), offsetof(struct ether_hdr, s_addr), 5, sizeof(uint8_t), "f"},
};
#define KLEE_TRACE_MBUF(m_ptr, dir)                                                                                                    \
  klee_trace_param_ptr_directed(m_ptr, sizeof(*m_ptr), #m_ptr, dir);                                                                   \
  klee_trace_param_ptr_field_directed(m_ptr, offsetof(struct rte_mbuf, buf_addr), sizeof(struct stub_mbuf_content*), "buf_addr", dir); \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) {                                                               \
    klee_trace_param_ptr_field_directed(m_ptr,                                                                                         \
                                        mbuf_descrs[i].offset,                                                                         \
                                        mbuf_descrs[i].width,                                                                          \
                                        mbuf_descrs[i].name,                                                                           \
                                        dir);                                                                                          \
  }
#define KLEE_TRACE_MBUF_EPTR(m_ptr, pname, dir)                                                                               \
  klee_trace_extra_ptr(m_ptr, sizeof(*m_ptr), pname, "", dir);                                                                \
  klee_trace_extra_ptr_field(m_ptr, offsetof(struct rte_mbuf, buf_addr), sizeof(struct stub_mbuf_content*), "buf_addr", dir); \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) {                                                      \
    klee_trace_extra_ptr_field(m_ptr,                                                                                         \
                               mbuf_descrs[i].offset,                                                                         \
                               mbuf_descrs[i].width,                                                                          \
                               mbuf_descrs[i].name,                                                                           \
                               dir);                                                                                          \
  }
#define KLEE_TRACE_MBUF_CONTENT(u_ptr, dir)                                                                             \
  klee_trace_extra_ptr(u_ptr, sizeof(struct stub_mbuf_content), "user_buf_addr", "", dir);                              \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, ether), sizeof(struct ether_hdr), "ether", dir); \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, ipv4), sizeof(struct ipv4_hdr), "ipv4", dir);    \
  klee_trace_extra_ptr_field(u_ptr, offsetof(struct stub_mbuf_content, tcp), sizeof(struct tcp_hdr), "tcp", dir);       \
  for (int i = 0; i < sizeof(stub_mbuf_content_nested)/sizeof(stub_mbuf_content_nested[0]); ++i) {                      \
    klee_trace_extra_ptr_nested_field(u_ptr,                                                                            \
                                      stub_mbuf_content_nested[i].base_offset,                                          \
                                      stub_mbuf_content_nested[i].offset,                                               \
                                      stub_mbuf_content_nested[i].width,                                                \
                                      stub_mbuf_content_nested[i].name,                                                 \
                                      dir);                                                                             \
  }                                                                                                                     \
  for (int i = 0; i < sizeof(stub_mbuf_content_n2)/sizeof(stub_mbuf_content_n2[0]); ++i) {                              \
    klee_trace_extra_ptr_nested_nested_field                                                                            \
      (u_ptr,                                                                                                           \
       stub_mbuf_content_n2[i].base_base_offset,                                                                        \
       stub_mbuf_content_n2[i].base_offset,                                                                             \
       stub_mbuf_content_n2[i].offset,                                                                                  \
       stub_mbuf_content_n2[i].width,                                                                                   \
       stub_mbuf_content_n2[i].name,                                                                                    \
       dir);                                                                                                            \
  }
// END TRACING

void
stub_free(struct rte_mbuf* mbuf) {
	klee_trace_ret();
	klee_trace_param_just_ptr(mbuf, sizeof(struct rte_mbuf), "mbuf");

	klee_alias_function("rte_pktmbuf_free", "rte_pktmbuf_free");
	rte_pktmbuf_free(mbuf);
	klee_alias_function("rte_pktmbuf_free", "stub_free");
}

static uint16_t
stub_rx(void* q, struct rte_mbuf** bufs, uint16_t nb_bufs)
{
	klee_trace_ret();
	klee_trace_param_ptr_directed(q, sizeof(struct stub_queue), "q", TD_IN);
	klee_trace_param_ptr_field_directed(q, offsetof(struct stub_queue, port_id), sizeof(uint16_t), "port_id", TD_IN);
	klee_trace_param_ptr_directed(bufs, sizeof(struct rte_mbuf*), "mbuf", TD_OUT);
	klee_trace_param_u16(nb_bufs, "nb_bufs");

	struct stub_queue* stub_q = q;

	uint16_t priv_size = rte_pktmbuf_priv_size(stub_q->mb_pool);
	uint16_t mbuf_size = sizeof(struct rte_mbuf) + priv_size;
	uint16_t buf_len = rte_pktmbuf_data_room_size(stub_q->mb_pool);

	int received = klee_range(0, nb_bufs + 1 /* end is exclusive */, "received");
	if (received) {
		int i = 0;
		for (i = 0; i < received; i++) {
			bufs[i] = rte_mbuf_raw_alloc(stub_q->mb_pool);
			if (!bufs[i]) {
				break;
			}

			struct rte_mbuf* buf_symbol = (struct rte_mbuf*) malloc(stub_q->mb_pool->elt_size);
			if (buf_symbol == NULL) {
				rte_pktmbuf_free(bufs[i]);
				break;
			}

			// Make the packet symbolic
			klee_make_symbolic(buf_symbol, stub_q->mb_pool->elt_size, "buf_value");
			memcpy(bufs[i], buf_symbol, stub_q->mb_pool->elt_size);
			free(buf_symbol);

			// Explicitly make the content symbolic
			struct stub_mbuf_content* buf_content_symbol = (struct stub_mbuf_content*) malloc(sizeof(struct stub_mbuf_content));
			if (buf_content_symbol == NULL) {
				rte_pktmbuf_free(bufs[i]);
				break;
			}
			klee_make_symbolic(buf_content_symbol, sizeof(struct stub_mbuf_content), "user_buf");
			memcpy((char*) bufs[i] + mbuf_size, buf_content_symbol, sizeof(struct stub_mbuf_content));
			free(buf_content_symbol);

			// Keep contrete values for what a driver guarantees
			// (assignments are in the same order as the rte_mbuf declaration)
			bufs[i]->buf_addr = (char*) bufs[i] + mbuf_size;
			bufs[i]->buf_physaddr = rte_mempool_virt2phy(stub_q->mb_pool, bufs[i]) + mbuf_size;
			bufs[i]->buf_len = (uint16_t) buf_len;
			// TODO: make data_off symbolic (but then we get symbolic pointer addition...)
			// Alternative: Somehow prove that the code never touches anything outside of the [data_off, data_off+data_len] range...
			bufs[i]->data_off = 0; // klee_range(0, stub_q->mb_pool->elt_size - sizeof(struct stub_mbuf_content), "data_off");
			bufs[i]->refcnt = 1;
			bufs[i]->nb_segs = 1; // TODO do we want to make a possibility of multiple packets? Or we could just prove the NF never touches this...
			bufs[i]->port = stub_q->port_id;
			bufs[i]->ol_flags = 0;
			// packet_type is symbolic
			bufs[i]->pkt_len = sizeof(struct stub_mbuf_content);
			bufs[i]->data_len = sizeof(struct stub_mbuf_content);
			// vlan_tci is symbolic
			// hash is symbolic
			// seqn is symbolic
			// vlan_tci_outer is symbolic
			bufs[i]->userdata = NULL;
			bufs[i]->pool = stub_q->mb_pool;
			bufs[i]->next = NULL;
			// tx_offload is symbolic
			bufs[i]->priv_size = priv_size;
			// timesync is symbolic

			rte_mbuf_sanity_check(bufs[i], 1 /* is head mbuf */);

			struct stub_mbuf_content* buf_content = rte_pktmbuf_mtod(bufs[i], struct stub_mbuf_content*);
			// TODO this matches nf_util, fix at the same time
			if(RTE_ETH_IS_IPV4_HDR(bufs[i]->packet_type) ||
				(bufs[i]->packet_type == 0 && buf_content->ether.ether_type == rte_cpu_to_be_16(ETHER_TYPE_IPv4))) {
				buf_content->ipv4.total_length = rte_cpu_to_be_16(sizeof(struct ipv4_hdr) + sizeof(struct tcp_hdr));
			}

			if (i == 0) { // TODO should trace every packet... but for now there's only 1 anyway
				// Packet is actually received, trace it now
				// FIXME replacing 0 by i here causes KLEE to fail...
				KLEE_TRACE_MBUF_EPTR(bufs[0], "incoming_package", TD_OUT);
				KLEE_TRACE_MBUF_CONTENT(bufs[0]->buf_addr, TD_OUT);
			}

		}

		return i;
	}

	return 0;
}

static uint16_t
stub_tx(void* q, struct rte_mbuf** bufs, uint16_t nb_bufs)
{
	klee_trace_ret();
	klee_trace_param_ptr_directed(q, sizeof(struct stub_queue), "q", TD_IN);
	klee_trace_param_ptr_field_directed(q, offsetof(struct stub_queue, port_id), sizeof(uint16_t), "port_id", TD_IN);
	klee_trace_param_ptr_directed(bufs, sizeof(struct rte_mbuf*), "mbuf", TD_IN);
	klee_trace_param_u16(nb_bufs, "nb_bufs");

	int packets_sent = klee_range(0, nb_bufs + 1 /* end is exclusive */, "packets_sent");
	int i;
	for (i = 0; i < packets_sent; i++) {
		rte_pktmbuf_free(bufs[i]);
	}
	return i;
}

static int
stub_dev_configure(struct rte_eth_dev *dev)
{
	return 0;
}

static int
stub_dev_start(struct rte_eth_dev *dev)
{
	dev->data->dev_link.link_status = ETH_LINK_UP;
	return 0;
}

static void
stub_dev_stop(struct rte_eth_dev *dev)
{
	dev->data->dev_link.link_status = ETH_LINK_DOWN;
}

static int
stub_rx_queue_setup(struct rte_eth_dev *dev, uint16_t rx_queue_id,
		uint16_t nb_rx_desc,
		unsigned int socket_id,
		const struct rte_eth_rxconf *rx_conf,
		struct rte_mempool *mb_pool)
{
	if (rx_queue_id >= dev->data->nb_rx_queues) {
		return -ENODEV;
	}

	struct stub_device* device = dev->data->dev_private;
	device->rx_queues[rx_queue_id].port_id = dev->data->port_id;
	device->rx_queues[rx_queue_id].mb_pool = mb_pool;

	dev->data->rx_queues[rx_queue_id] = &device->rx_queues[rx_queue_id];

	return 0;
}

static int
stub_tx_queue_setup(struct rte_eth_dev *dev, uint16_t tx_queue_id,
		uint16_t nb_tx_desc,
		unsigned int socket_id,
		const struct rte_eth_txconf *tx_conf)
{
	if (tx_queue_id >= dev->data->nb_tx_queues) {
		return -ENODEV;
	}

	struct stub_device* device = dev->data->dev_private;
	device->tx_queues[tx_queue_id].port_id = dev->data->port_id;
	device->tx_queues[tx_queue_id].mb_pool = NULL;

	dev->data->tx_queues[tx_queue_id] = &device->tx_queues[tx_queue_id];

	return 0;
}


static void
stub_queue_release(void *q)
{
	klee_abort();
}

static void
stub_dev_info(struct rte_eth_dev *dev,
		struct rte_eth_dev_info *dev_info)
{
	dev_info->driver_name = stub_name;
	dev_info->max_mac_addrs = 1;
	dev_info->max_rx_pktlen = (uint32_t) -1;
	dev_info->max_rx_queues = 1;
	dev_info->max_tx_queues = 1;
	dev_info->min_rx_bufsize = 0;
	dev_info->pci_dev = NULL;
	dev_info->reta_size = 0;
	dev_info->flow_type_rss_offloads = 0;
}

static void
stub_stats_get(struct rte_eth_dev *dev, struct rte_eth_stats *igb_stats)
{
	klee_abort();
}

static void
stub_stats_reset(struct rte_eth_dev *dev)
{
	klee_abort();
}

static int
stub_link_update(struct rte_eth_dev *dev, int wait_to_complete)
{
	return 0; // DPDK doesn't even check the return value anyway...
}

static int
stub_rss_reta_update(struct rte_eth_dev *dev, struct rte_eth_rss_reta_entry64 *reta_conf, uint16_t reta_size)
{
	klee_abort();
}

static int
stub_rss_reta_query(struct rte_eth_dev *dev, struct rte_eth_rss_reta_entry64 *reta_conf, uint16_t reta_size)
{
	klee_abort();
}

static int
stub_rss_hash_update(struct rte_eth_dev *dev, struct rte_eth_rss_conf *rss_conf)
{
	klee_abort();
}

static int
stub_rss_hash_conf_get(struct rte_eth_dev *dev,
		struct rte_eth_rss_conf *rss_conf)
{
	klee_abort();
}

static const struct eth_dev_ops stub_ops = {
	.dev_start = stub_dev_start,
	.dev_stop = stub_dev_stop,
	.dev_configure = stub_dev_configure,
	.dev_infos_get = stub_dev_info,
	.rx_queue_setup = stub_rx_queue_setup,
	.tx_queue_setup = stub_tx_queue_setup,
	.rx_queue_release = stub_queue_release,
	.tx_queue_release = stub_queue_release,
	.link_update = stub_link_update,
	.stats_get = stub_stats_get,
	.stats_reset = stub_stats_reset,
	.reta_update = stub_rss_reta_update,
	.reta_query = stub_rss_reta_query,
	.rss_hash_update = stub_rss_hash_update,
	.rss_hash_conf_get = stub_rss_hash_conf_get
};

int
stub_dev_create(const char *name,
		const unsigned numa_node)
{
	struct rte_eth_dev_data* data = (struct rte_eth_dev_data*) malloc(sizeof(struct rte_eth_dev_data));
	if (data == NULL) {
		return -1;
	}

	struct stub_device* device = (struct stub_device*) malloc(sizeof(struct stub_device));
	if (device == NULL) {
		free(data);
		return -1;
	}

	struct rte_eth_dev* eth_dev = rte_eth_dev_allocate(name, RTE_ETH_DEV_VIRTUAL);
	if (eth_dev == NULL) {
		free(data);
		free(device);
		return -1;
	}

	data->dev_private = device;
	data->port_id = eth_dev->data->port_id;
	data->rx_queues = NULL;
	data->nb_rx_queues = 0;
	data->tx_queues = NULL;
	data->nb_tx_queues = 0;
        data->dev_started = 0;
	data->dev_link = stub_link;
	data->mac_addrs = &stub_addr;
	strncpy(data->name, eth_dev->data->name, strlen(eth_dev->data->name));
	data->dev_flags = 0;
	data->kdrv = RTE_KDRV_NONE;
	data->drv_name = stub_name;
	data->numa_node = numa_node;

	eth_dev->data = data;
	eth_dev->dev_ops = &stub_ops;
	TAILQ_INIT(&eth_dev->link_intr_cbs);
	eth_dev->driver = NULL;
	eth_dev->rx_pkt_burst = stub_rx;
	eth_dev->tx_pkt_burst = stub_tx;

	return 0;

error:
	free(data);
	free(device);

	return -1;
}

static int
stub_devinit(const char *name, const char *params)
{
	// name is always NULL

	unsigned numa_node = rte_socket_id();

	for (int n = 0; n < RTE_MAX_ETHPORTS; n++) {
		int ret = stub_dev_create(stub_name, numa_node);
		if (ret != 0) {
			return ret;
		}
	}

	return 0;
}

static int
stub_devuninit(const char *name)
{
	// name is always NULL

	struct rte_eth_dev* eth_dev = rte_eth_dev_allocated(stub_name);
	if (eth_dev == NULL) {
		return -1;
	}

	free(eth_dev->data->dev_private);
	free(eth_dev->data);

	rte_eth_dev_release_port(eth_dev);

	return 0;
}

struct rte_driver stub_driver = {
	.name = RTE_STR(stub_name),
	.type = PMD_PDEV,
	.init = stub_devinit,
	.uninit = stub_devuninit,
};

void
stub_init(void)
{
	klee_alias_function("rte_pktmbuf_free", "stub_free"); // HACK
	// HACK clang, what u doin?
	klee_alias_function("rte_pktmbuf_free941", "stub_free");
	klee_alias_function("rte_pktmbuf_free1119", "stub_free");
	klee_alias_function("rte_pktmbuf_free1156", "stub_free");
	klee_alias_function("rte_pktmbuf_free1185", "stub_free");
	klee_alias_function("rte_pktmbuf_free1223", "stub_free");
	klee_alias_function("rte_pktmbuf_free1319", "stub_free");
	klee_alias_function("rte_pktmbuf_free1663", "stub_free");
	klee_alias_function("rte_pktmbuf_free1743", "stub_free");
	klee_alias_function("rte_pktmbuf_free1777", "stub_free");
	klee_alias_function("rte_pktmbuf_free1817", "stub_free");
	klee_alias_function("rte_pktmbuf_free1852", "stub_free");
	klee_alias_function("rte_pktmbuf_free1893", "stub_free");
	klee_alias_function("rte_pktmbuf_free1927", "stub_free");
	klee_alias_function("rte_pktmbuf_free1970", "stub_free");
	klee_alias_function("rte_pktmbuf_free2023", "stub_free");
	klee_alias_function("rte_pktmbuf_free2104", "stub_free");
	klee_alias_function("rte_pktmbuf_free2305", "stub_free");
	rte_eal_driver_register(&stub_driver);
}
