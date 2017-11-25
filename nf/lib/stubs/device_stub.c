// Inspired from the DPDK null driver

#include <device_stub.h>

#include <klee/klee.h>

#include "containers/str-descr.h"

#include <rte_dev.h>
#include <rte_ethdev.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_memcpy.h>
#include <rte_tcp.h>

#define STUB_DEVICES_COUNT 2
#define STUB_PACKET_SIZE 64

// Arseniy's black magic, TODO understand it
struct user_buf {
  struct ether_hdr ether;
  struct ipv4_hdr ipv4;
  struct tcp_hdr tcp;
};
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
  klee_trace_extra_ptr(m_ptr, sizeof(*(m_ptr)), pname, "");                \
  klee_trace_extra_ptr_field(m_ptr, offsetof(struct rte_mbuf, buf_addr), \
                             sizeof(struct user_buf*), "buf_addr");     \
  for (int i = 0; i < sizeof(mbuf_descrs)/sizeof(mbuf_descrs[0]); ++i) { \
    klee_trace_extra_ptr_field(m_ptr,                                   \
                               mbuf_descrs[i].offset,                   \
                               mbuf_descrs[i].width,                    \
                               mbuf_descrs[i].name);                    \
  }


static const char* stub_name = "stub";
static struct ether_addr stub_addr = { .addr_bytes = {0} };
static struct rte_eth_link stub_link = {
	.link_speed = ETH_SPEED_NUM_10G,
	.link_duplex = ETH_LINK_FULL_DUPLEX,
	.link_status = ETH_LINK_DOWN,
	.link_autoneg = ETH_LINK_SPEED_AUTONEG,
};

struct stub_queue {
	struct rte_mempool* mb_pool;
	uint16_t port_id;
};

struct stub_device {
	struct stub_queue rx_queues[RTE_MAX_QUEUES_PER_PORT];
	struct stub_queue tx_queues[RTE_MAX_QUEUES_PER_PORT];
};

static uint16_t
stub_rx(void *q, struct rte_mbuf **bufs, uint16_t nb_bufs)
{
	if (nb_bufs == 0) {
		return 0;
	}

	struct stub_queue *stub_q = q;

	int received = klee_range(0, nb_bufs + 1 /* end is exclusive */, "received");
	if (received) {
/*		klee_trace_ret();
		klee_trace_param_i32(stub_q->device->port_id, "received_packet_device");
		klee_trace_param_ptr(bufs, sizeof(struct rte_mbuf*), "mbuf");
		KLEE_TRACE_MBUF_EPTR(&(stub_q->device->incoming_package), "incoming_package");
		KLEE_TRACE_USER_BUF(&(stub_q->device->user_buf));
		klee_allow_access(&(stub_q->device->user_buf), sizeof(struct user_buf));
		klee_allow_access(&(stub_q->device->incoming_package), sizeof(struct rte_mbuf));
		klee_assert(!stub_q->device->incoming_package_allocated);*/

		received = 1; // TODO support more than one

		int i = 0;
		for (i = 0; i < received; i++) {
			bufs[i] = rte_pktmbuf_alloc(stub_q->mb_pool);
			if (!bufs[i]) {
				break;
			}
			bufs[i]->data_len = STUB_PACKET_SIZE;
			bufs[i]->pkt_len = STUB_PACKET_SIZE;
			bufs[i]->nb_segs = 1;
			bufs[i]->next = NULL;
			bufs[i]->port = stub_q->port_id;

			// TODO realistic packets...
			int is_ipv4 = klee_int("is_ipv4");
			if (is_ipv4) {
				bufs[i]->packet_type = RTE_PTYPE_L3_IPV4;
				struct ipv4_hdr* ipv4_header = rte_pktmbuf_mtod_offset(bufs[i], struct ipv4_hdr*, sizeof(struct ether_hdr));

				int tcpudp_type = klee_range(0, 3, "tcpudp_type");
				if (tcpudp_type == 0) {
					ipv4_header->next_proto_id = IPPROTO_IP;
				} else if (tcpudp_type == 1) {
					ipv4_header->next_proto_id = IPPROTO_TCP;
				} else {
					ipv4_header->next_proto_id = IPPROTO_UDP;
				}
			} else {
				bufs[i]->packet_type = RTE_PTYPE_UNKNOWN;
			}
		}
		return i;
	}

	return 0;
}

static uint16_t
stub_tx(void *q, struct rte_mbuf **bufs, uint16_t nb_bufs)
{
	if (nb_bufs == 0) {
		return 0;
	}
	if (nb_bufs > 1) {
		klee_abort(); // TODO support more than one
	}

	struct stub_queue *stub_q = q;

/*	klee_trace_ret();
	KLEE_TRACE_MBUF(bufs[0], TD_IN);
	KLEE_TRACE_USER_BUF(bufs[0]->buf_addr);
	klee_trace_param_i32(stub_q->device->port_id, "portid");*/
	int packets_sent = klee_range(0, nb_bufs + 1 /* end is exclusive */, "packets_sent");
	for (int i = 0; i < packets_sent; i++) {
		rte_pktmbuf_free(bufs[i]);
/*		klee_forbid_access(bufs[0]->buf_addr, sizeof(struct user_buf), "pkt sent");
		klee_forbid_access(bufs[0], sizeof(struct rte_mbuf), "pkt sent");*/
	}
	return packets_sent;
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

	for (int n = 0; n < STUB_DEVICES_COUNT; n++) {
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
