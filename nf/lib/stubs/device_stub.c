// Inspired from the DPDK null driver

#include <device_stub.h>

#include <inttypes.h>

#include <klee/klee.h>

#include <rte_byteorder.h>
#include <rte_dev.h>
#include <rte_ethdev.h>
#include <rte_ip.h>
#include <rte_mbuf.h>
#include <rte_tcp.h>

// TODO more complete stub content?
// do change the total_len in rx if this is changed!
struct stub_mbuf_content {
  struct ether_hdr ether;
  struct ipv4_hdr ipv4;
  struct tcp_hdr tcp;
};

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
	struct stub_queue *stub_q = q;

	int received = klee_range(0, nb_bufs + 1 /* end is exclusive */, "received");
	if (received) {
		int i = 0;
		for (i = 0; i < received; i++) {
			// Use raw_alloc for now, we reset it later after making it symbolic
			bufs[i] = rte_mbuf_raw_alloc(stub_q->mb_pool);
			if (!bufs[i]) {
				break;
			}

			struct rte_mbuf* buf_value = (struct rte_mbuf*) malloc(stub_q->mb_pool->elt_size);
			if (buf_value == NULL) {
				rte_pktmbuf_free(bufs[i]);
				break;
			}

			// Make the packet symbolic...
			klee_make_symbolic(buf_value, stub_q->mb_pool->elt_size, "buf_value");
			memcpy(bufs[i], buf_value, stub_q->mb_pool->elt_size);
			free(buf_value);

			// ...except for what a driver guarantees
			// (assignments are in the same order as the rte_mbuf declaration)
			uint16_t priv_size = rte_pktmbuf_priv_size(stub_q->mb_pool);
			uint16_t mbuf_size = sizeof(struct rte_mbuf) + priv_size;
			uint16_t buf_len = rte_pktmbuf_data_room_size(stub_q->mb_pool);
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

	struct stub_queue *stub_q = q;
	int packets_sent = klee_range(0, nb_bufs + 1 /* end is exclusive */, "packets_sent");
	for (int i = 0; i < packets_sent; i++) {
		rte_pktmbuf_free(bufs[i]);
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
