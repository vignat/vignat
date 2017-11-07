// Inspired from the DPDK null driver

#include <device_stub.h>

#include <klee/klee.h>

#include <rte_mbuf.h>
#include <rte_ethdev.h>
#include <rte_memcpy.h>
#include <rte_dev.h>

#define STUB_DEVICES_COUNT 2
#define STUB_PACKET_SIZE 64

static const char* stub_name = "stub";
static struct ether_addr stub_addr = { .addr_bytes = {0} };
static struct rte_eth_link stub_link = {
	.link_speed = ETH_SPEED_NUM_10G,
	.link_duplex = ETH_LINK_FULL_DUPLEX,
	.link_status = ETH_LINK_DOWN,
	.link_autoneg = ETH_LINK_SPEED_AUTONEG,
};

struct stub_device;

struct stub_queue {
	struct stub_device* device;
	struct rte_mempool* mb_pool;
};

struct stub_device {
	uint16_t port_id;
	struct stub_queue rx_queues[RTE_MAX_QUEUES_PER_PORT];
	struct stub_queue tx_queues[RTE_MAX_QUEUES_PER_PORT];
};

static uint16_t
stub_rx(void *q, struct rte_mbuf **bufs, uint16_t nb_bufs)
{
	int i;
	struct stub_queue *stub_q = q;
	for (i = 0; i < nb_bufs; i++) {
		bufs[i] = rte_pktmbuf_alloc(stub_q->mb_pool);
		if (!bufs[i]) {
			break;
		}

		bufs[i]->data_len = STUB_PACKET_SIZE;
		bufs[i]->pkt_len = STUB_PACKET_SIZE;
		bufs[i]->nb_segs = 1;
		bufs[i]->next = NULL;
		bufs[i]->port = stub_q->device->port_id;
	}

	return i;
}

static uint16_t
stub_tx(void *q, struct rte_mbuf **bufs, uint16_t nb_bufs)
{
	for (int i = 0; i < nb_bufs; i++) {
		rte_pktmbuf_free(bufs[i]);
	}

	return nb_bufs;
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
	device->rx_queues[rx_queue_id].device = device;
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
	device->tx_queues[tx_queue_id].device = device;
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
	struct rte_eth_dev* eth_dev = rte_eth_dev_allocate(name, RTE_ETH_DEV_VIRTUAL);
	if (eth_dev == NULL) {
		goto error;
	}

	struct rte_eth_dev_data* data = (struct rte_eth_dev_data*) malloc(sizeof(struct rte_eth_dev_data));
	if (data == NULL) {
		goto error;
	}

	struct stub_device* device = (struct stub_device*) malloc(sizeof(struct stub_device));
	if (device == NULL) {
		goto error;
	}

	device->port_id = eth_dev->data->port_id;

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
	//data->dev_flags = RTE_ETH_DEV_DETACHABLE;
	//data->kdrv = RTE_KDRV_NONE;
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
