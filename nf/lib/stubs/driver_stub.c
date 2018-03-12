// Inspired from the DPDK null driver

#include "lib/stubs/driver_stub.h"
#include "lib/stubs/core_stub.h"

#include <rte_bus_vdev.h>
#include <rte_ethdev.h>
#include <rte_ethdev_vdev.h>
#include <rte_malloc.h>
#include <rte_mbuf.h>

#include <klee/klee.h>


// Constant stuff
static const int DEVICES_COUNT = 2; // more devices = lots more paths in the NF
static const char* stub_driver_names[DEVICES_COUNT] = { "stub0", "stub1" }; // don't rely on snprintf
static struct ether_addr stub_addr = { .addr_bytes = {0} };
static struct rte_eth_link stub_link = {
	.link_speed = ETH_SPEED_NUM_10G,
	.link_duplex = ETH_LINK_FULL_DUPLEX,
	.link_status = ETH_LINK_DOWN,
	.link_autoneg = ETH_LINK_SPEED_AUTONEG
};


// Sanity checks
static bool device_created[RTE_MAX_ETHPORTS];
static bool device_configured[RTE_MAX_ETHPORTS];
static bool device_started[RTE_MAX_ETHPORTS];
static bool device_rx_setup[RTE_MAX_ETHPORTS]; // we support only 1 queue per device
static bool device_tx_setup[RTE_MAX_ETHPORTS];


// Globals
static struct rte_vdev_driver stub_drivers[DEVICES_COUNT];

void
stub_free(struct rte_mbuf* mbuf) {
	// Undo alias, since otherwise it will recurse infinitely
	klee_alias_undo("rte_pktmbuf_free[0-9]*");
	stub_core_mbuf_free(mbuf);
	klee_alias_function_regex("rte_pktmbuf_free[0-9]*", "stub_free");
}

static uint16_t
stub_rx(void* q, struct rte_mbuf** bufs, uint16_t nb_bufs)
{
	klee_assert(q != NULL);
	klee_assert(nb_bufs == 1); // :(

	struct stub_queue* stub_q = q;

	klee_assert(device_created[stub_q->port_id]);
	klee_assert(device_configured[stub_q->port_id]);
	klee_assert(device_started[stub_q->port_id]);
	klee_assert(device_rx_setup[stub_q->port_id]);

	if (klee_int("received") == 0) {
		return 0;
	}

	if (!stub_core_mbuf_create(stub_q->port_id, stub_q->mb_pool, bufs)) {
		return 0;
	}

	stub_core_trace_rx(bufs[0]);
	return 1;
}

static uint16_t
stub_tx(void* q, struct rte_mbuf** bufs, uint16_t nb_bufs)
{
	klee_assert(q != NULL);
	klee_assert(nb_bufs == 1); // :(

	struct stub_queue* stub_q = q;

	klee_assert(device_created[stub_q->port_id]);
	klee_assert(device_configured[stub_q->port_id]);
	klee_assert(device_started[stub_q->port_id]);
	klee_assert(device_rx_setup[stub_q->port_id]);

	if (klee_int("sent") == 0) {
		return 0;
	}

	stub_core_trace_tx(bufs[0], stub_q->port_id);
	stub_core_mbuf_free(bufs[0]);
	return 1;
}

static int
stub_dev_configure(struct rte_eth_dev *dev)
{
	struct stub_driver* stub_drv = dev->data->dev_private;

	klee_assert(device_created[stub_drv->port_id]);
	klee_assert(!device_configured[stub_drv->port_id]);

	int ret = klee_int("dev_configure_return");

	if (ret == 0) {
		device_configured[stub_drv->port_id] = true;
	}

	return ret;
}

static int
stub_dev_start(struct rte_eth_dev *dev)
{
	struct stub_driver* stub_drv = dev->data->dev_private;

	klee_assert(device_created[stub_drv->port_id]);
	klee_assert(device_configured[stub_drv->port_id]);
	klee_assert(device_rx_setup[stub_drv->port_id]);
	klee_assert(device_tx_setup[stub_drv->port_id]);
	klee_assert(!device_started[stub_drv->port_id]);

	int ret = klee_int("dev_start_return");

	if (ret == 0) {
		dev->data->dev_link.link_status = ETH_LINK_UP;
		device_started[stub_drv->port_id] = true;
	}

	return ret;
}

static void
stub_dev_stop(struct rte_eth_dev *dev)
{
	struct stub_driver* stub_drv = dev->data->dev_private;

	klee_assert(device_created[stub_drv->port_id]);
	klee_assert(device_configured[stub_drv->port_id]);
	klee_assert(device_started[stub_drv->port_id]);

	dev->data->dev_link.link_status = ETH_LINK_DOWN;
	device_started[stub_drv->port_id] = false;
}

static int
stub_rx_queue_setup(struct rte_eth_dev *dev, uint16_t rx_queue_id,
		uint16_t nb_rx_desc,
		unsigned int socket_id,
		const struct rte_eth_rxconf *rx_conf,
		struct rte_mempool *mb_pool)
{
	struct stub_driver* stub_drv = dev->data->dev_private;

	klee_assert(device_created[stub_drv->port_id]);
	klee_assert(device_configured[stub_drv->port_id]);
	klee_assert(!device_rx_setup[stub_drv->port_id]);

	// Only 1 RX queue allowed
	klee_assert(rx_queue_id == 0);

	int ret = klee_int("dev_rx_queue_setup_return");

	if (ret == 0) {
		stub_drv->rx_queues[rx_queue_id].port_id = stub_drv->port_id;
		stub_drv->rx_queues[rx_queue_id].mb_pool = mb_pool;
		dev->data->rx_queues[rx_queue_id] = &stub_drv->rx_queues[rx_queue_id];
		device_rx_setup[stub_drv->port_id] = true;
	}

	return ret;
}

static int
stub_tx_queue_setup(struct rte_eth_dev *dev, uint16_t tx_queue_id,
		uint16_t nb_tx_desc,
		unsigned int socket_id,
		const struct rte_eth_txconf *tx_conf)
{
	struct stub_driver* stub_drv = dev->data->dev_private;

	klee_assert(device_created[stub_drv->port_id]);
	klee_assert(device_configured[stub_drv->port_id]);
	klee_assert(!device_tx_setup[stub_drv->port_id]);

	// Only 1 TX queue allowed
	klee_assert(tx_queue_id == 0);

	int ret = klee_int("dev_tx_queue_setup_return");

	if (ret == 0) {
		stub_drv->tx_queues[tx_queue_id].port_id = stub_drv->port_id;
		stub_drv->tx_queues[tx_queue_id].mb_pool = NULL;
		dev->data->tx_queues[tx_queue_id] = &stub_drv->tx_queues[tx_queue_id];
		device_tx_setup[stub_drv->port_id] = true;
	}

	return ret;
}

static void
stub_queue_release(void *queue)
{
	klee_assert(queue != NULL);

	struct stub_queue* stub_queue = queue;

	bool queue_found = false;

	// First, find the queue we're releasing
	for (int d = 0; d < DEVICES_COUNT; d++) {
		struct rte_eth_dev* dev = rte_eth_dev_allocated(stub_drivers[d].driver.name);
		struct stub_driver* stub_drv = dev->data->dev_private;

		for (int q = 0; q < RTE_MAX_QUEUES_PER_PORT; q++) {
			// Second, reset the associated state and progress
			if (&stub_drv->rx_queues[q] == stub_queue) {
				klee_assert(!queue_found);
				klee_assert(device_rx_setup[stub_drv->port_id]);

				dev->data->rx_queues[q] = NULL;
				device_rx_setup[stub_drv->port_id] = false;
				memset(stub_queue, 0, sizeof(struct stub_queue));
				queue_found = true;
			} else if (&stub_drv->tx_queues[q] == stub_queue) {
				klee_assert(!queue_found);
				klee_assert(device_tx_setup[stub_drv->port_id]);

				dev->data->tx_queues[q] = NULL;
				device_tx_setup[stub_drv->port_id] = false;
				memset(stub_queue, 0, sizeof(struct stub_queue));
				queue_found = true;
			}
		}
	}

	klee_assert(queue_found);
}

static void
stub_dev_info(struct rte_eth_dev *dev,
		struct rte_eth_dev_info *dev_info)
{
	struct stub_driver* stub_drv = dev->data->dev_private;

	klee_assert(device_created[stub_drv->port_id]);

	dev_info->driver_name = "stub";
	dev_info->max_mac_addrs = 1;
	dev_info->max_rx_pktlen = (uint32_t) -1;
	dev_info->max_rx_queues = RTE_DIM(stub_drv->rx_queues);
	dev_info->max_tx_queues = RTE_DIM(stub_drv->tx_queues);
	dev_info->min_rx_bufsize = 0;
	dev_info->pci_dev = NULL;
	dev_info->reta_size = 0;
	dev_info->flow_type_rss_offloads = 0;
}

static int
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
	// TODO what to do here?
	return klee_int("dev_link_update_return");
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
stub_rss_hash_conf_get(struct rte_eth_dev *dev, struct rte_eth_rss_conf *rss_conf)
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

static int
stub_driver_probe(struct rte_vdev_device* vdev)
{
        int ret = klee_int("stub_driver_probe_return");
        if (ret != 0) {
                return ret;
        }

	if (vdev == NULL) {
		klee_abort();
	}

	// not sure why this is needed but it's in eth_null
	if (vdev->device.numa_node == SOCKET_ID_ANY) {
		vdev->device.numa_node = rte_socket_id();
	}

	struct rte_eth_dev* dev = rte_eth_vdev_allocate(vdev, sizeof(struct stub_driver));

	if (dev == NULL) {
		return -ENOMEM;
	}

	struct stub_driver* stub_drv = (struct stub_driver*) dev->data->dev_private;
	stub_drv->port_id = dev->data->port_id;

	klee_assert(!device_created[stub_drv->port_id]);

	dev->data->rx_queues = NULL;
	dev->data->nb_rx_queues = 0;
	dev->data->tx_queues = NULL;
	dev->data->nb_tx_queues = 0;
	dev->data->dev_started = 0;
	dev->data->dev_link = stub_link;
	dev->data->mac_addrs = &stub_addr;

	dev->dev_ops = &stub_ops;
	dev->rx_pkt_burst = stub_rx;
	dev->tx_pkt_burst = stub_tx;

	device_created[stub_drv->port_id] = true;

	return 0;
}

static int
stub_driver_remove(struct rte_vdev_device* vdev)
{
	int ret = klee_int("stub_driver_remove_return");
	if (ret != 0) {
		return ret;
	}

	if (vdev == NULL) {
		klee_abort();
	}

	struct rte_eth_dev* dev = rte_eth_dev_allocated(rte_vdev_device_name(vdev));
	if (dev == NULL) {
		klee_abort();
	}

	rte_free(dev->data->dev_private);
	rte_free(dev->data);

	rte_eth_dev_release_port(dev);

	return 0;
}


// First part of init
__attribute__((constructor))
static void
stub_driver_init(void)
{
#ifndef ENABLE_HARDWARE_STUB
	// Trace the packet free; need a regex to alias the duplicated functions
	// since rte_pktmbuf_free is inline (so there's e.g. rte_pktmbuf_free930)
	klee_alias_function_regex("rte_pktmbuf_free[0-9]*", "stub_free");

	for (int n = 0; n < DEVICES_COUNT; n++) {
		struct rte_vdev_driver rte_driver = {
			.next = NULL,
			.driver = {
				.next = NULL,
				.name = stub_driver_names[n],
				.alias = NULL,
			},
			.probe = stub_driver_probe,
			.remove = stub_driver_remove,
		};
		stub_drivers[n] = rte_driver;
		rte_vdev_register(&stub_drivers[n]);
	}
#endif
}

// Second part of init, after DPDK EAL init
void
stub_driver_attach(void)
{
	for (int n = 0; n < DEVICES_COUNT; n++) {
		int ret = rte_vdev_init(stub_driver_names[n], NULL);
		// should be 0, or the symbol returned by probe
		klee_assert(ret == 0 || klee_is_symbolic(ret));
	}
}
