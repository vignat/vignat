#include <inttypes.h>

#ifdef KLEE_VERIFICATION
#include <klee/klee.h>
#include "lib/stubs/my-time-stub-control.h"
#include "lib/stubs/device_stub.h"
#endif


#ifdef KLEE_VERIFICATION
#define VIGOR_LOOP_BEGIN \
  unsigned _vigor_lcore_id = rte_lcore_id(); \
  uint32_t _vigor_start_time = start_time(); \
  int _vigor_loop_termination = klee_int("loop_termination"); \
  nf_loop_iteration_begin(_vigor_lcore_id, _vigor_start_time); \
  while(klee_induce_invariants() & _vigor_loop_termination) { \
    nf_add_loop_iteration_assumptions(_vigor_lcore_id, _vigor_start_time); \
    uint32_t VIGOR_NOW = current_time(); \
    /* FIXME TODO TEMP HACK */ \
    unsigned _vigor_devices_count = rte_eth_dev_count(); \
    unsigned VIGOR_DEVICE = klee_range(0, _vigor_devices_count, "VIGOR_DEVICE"); \
    for(unsigned _ = 0; _ < _vigor_devices_count; _++) if (VIGOR_DEVICE == _) { VIGOR_DEVICE = _; break; }
#define VIGOR_LOOP_END \
    nf_loop_iteration_end(_vigor_lcore_id, VIGOR_NOW); \
  }
#else
#define VIGOR_LOOP_BEGIN \
  while (1) { \
    uint32_t VIGOR_NOW = current_time(); \
    unsigned _vigor_devices_count = rte_eth_dev_count(); \
    for (uint8_t VIGOR_DEVICE = 0; VIGOR_DEVICE < _vigor_devices_count; device++) {
#define VIGOR_LOOP_END } }
#endif


// DPDK uses these but doesn't include them. :|
#include <linux/limits.h>
#include <sys/types.h>

#include <rte_common.h>
#include <rte_eal.h>
#include <rte_ethdev.h>
#include <rte_launch.h>
#include <rte_lcore.h>
#include <rte_mbuf.h>
#include "rte_errno.h"

#include "lib/nf_forward.h"
#include "lib/nf_log.h"
#include "lib/nf_time.h"
#include "lib/nf_util.h"
#include <string.h>

// Queue sizes for receiving/transmitting packets (set to their values from l3fwd sample)
static const uint16_t RX_QUEUE_SIZE = 128;
static const uint16_t TX_QUEUE_SIZE = 512;

// Memory pool #buffers (set to its value from l3fwd sample)
#ifdef KLEE_VERIFICATION
// TODO this shouldn't be needed
static const unsigned MEMPOOL_BUFFER_COUNT = 1;
#else
static const unsigned MEMPOOL_BUFFER_COUNT = 8192;
#endif

// --- Initialization ---
static int
nf_init_device(uint8_t device, struct rte_mempool *mbuf_pool)
{
  int retval;

  // Configure the device
  // This is ugly code; DPDK samples use designated initializers,
  // but those are not available in C++, and this code needs to compile
  // both as C and C++.
  struct rte_eth_conf device_conf;
  memset(&device_conf, 0, sizeof(struct rte_eth_conf));
  device_conf.rxmode.mq_mode = ETH_MQ_RX_RSS;
  device_conf.rxmode.max_rx_pkt_len = ETHER_MAX_LEN;
  device_conf.rxmode.split_hdr_size = 0;
  device_conf.rxmode.header_split =   0;
  device_conf.rxmode.hw_ip_checksum = 1;
  device_conf.rxmode.hw_vlan_filter = 0;
  device_conf.rxmode.jumbo_frame =    0;
  device_conf.rxmode.hw_strip_crc =   0;
  device_conf.txmode.mq_mode = ETH_MQ_TX_NONE;
  device_conf.rx_adv_conf.rss_conf.rss_key = NULL;
  device_conf.rx_adv_conf.rss_conf.rss_hf = ETH_RSS_IP;

  retval = rte_eth_dev_configure(
    device, // The device
    1, // # of RX queues
    1, // # of TX queues
    &device_conf // device config
  );
  if (retval != 0) {
    rte_exit(EXIT_FAILURE, "Cannot configure device %" PRIu8 ", err=%d", device, retval);
  }

  // Allocate and set up 1 RX queue per device
  retval = rte_eth_rx_queue_setup(
    device, // device ID
    0, // queue ID
    RX_QUEUE_SIZE, // size
    rte_eth_dev_socket_id(device), // socket
    NULL, // config (NULL = default)
    mbuf_pool // memory pool
  );
  if (retval < 0) {
    rte_exit(EXIT_FAILURE, "Cannot allocate RX queue for device %" PRIu8 ", err=%d", device, retval);
  }

  // Allocate and set up 1 TX queue per device
  retval = rte_eth_tx_queue_setup(
    device, // device ID
    0, // queue ID
    TX_QUEUE_SIZE, // size
    rte_eth_dev_socket_id(device), // socket
    NULL // config (NULL = default)
  );
  if (retval < 0) {
    rte_exit(EXIT_FAILURE, "Cannot allocate TX queue for device %" PRIu8 " err=%d", device, retval);
  }

  // Start the device
  retval = rte_eth_dev_start(device);
  if (retval < 0) {
    rte_exit(EXIT_FAILURE, "Cannot start device on device %" PRIu8 ", err=%d", device, retval);
  }

  // Enable RX in promiscuous mode for the Ethernet device
  rte_eth_promiscuous_enable(device);

  return 0;
}

// --- Per-core work ---

//static __attribute__((noreturn)) // TODO make this work
void lcore_main(void)
{
  // TODO is this check useful?
  for (uint8_t device = 0; device < rte_eth_dev_count(); device++) {
    if (rte_eth_dev_socket_id(device) > 0 && rte_eth_dev_socket_id(device) != (int) rte_socket_id()) {
      NF_INFO("Device %" PRIu8 " is on remote NUMA node to polling thread.", device);
    }
  }

  nf_core_init();

  NF_INFO("Core %u forwarding packets.", rte_lcore_id());

  VIGOR_LOOP_BEGIN
    struct rte_mbuf* buf[1];
    uint16_t actual_rx_len = rte_eth_rx_burst(VIGOR_DEVICE, 0, buf, 1);

    if (actual_rx_len != 0) {
      uint8_t dst_device = nf_core_process(VIGOR_DEVICE, buf[0], VIGOR_NOW);
      if (dst_device == VIGOR_DEVICE) {
        rte_pktmbuf_free(buf[0]);
      } else {
        uint16_t actual_tx_len = rte_eth_tx_burst(dst_device, 0, buf, 1);
        if (actual_tx_len == 0) {
          rte_pktmbuf_free(buf[0]);
        }
      }
    }
  VIGOR_LOOP_END
}


// --- Main ---

int
main(int argc, char* argv[])
{
#ifdef KLEE_VERIFICATION
  rte_eal_driver_register(&stub_driver);
#endif

  // Initialize the Environment Abstraction Layer (EAL)
  int ret = rte_eal_init(argc, argv);
  if (ret < 0) {
    rte_exit(EXIT_FAILURE, "Error with EAL initialization, ret=%d\n", ret);
  }
  argc -= ret;
  argv += ret;

  nf_config_init(argc, argv);
  nf_print_config();

  // Create a memory pool
  unsigned nb_devices = rte_eth_dev_count();
  struct rte_mempool* mbuf_pool = rte_pktmbuf_pool_create(
    "MEMPOOL", // name
    MEMPOOL_BUFFER_COUNT * nb_devices, // #elements
    0, // cache size (per-lcore, not useful in a single-threaded app)
    0, // application private area size
    RTE_MBUF_DEFAULT_BUF_SIZE, // data buffer size
    rte_socket_id() // socket ID
  );
  if (mbuf_pool == NULL) {
    rte_exit(EXIT_FAILURE, "Cannot create mbuf pool\n");
  }

  // Initialize all devices
  for (uint8_t device = 0; device < nb_devices; device++) {
    if (nf_init_device(device, mbuf_pool) == 0) {
      NF_INFO("Initialized device %" PRIu8 ".", device);
    } else {
      rte_exit(EXIT_FAILURE, "Cannot init device %" PRIu8 ".", device);
    }
  }
  // Run!
  // ...in single-threaded mode, that is.
  lcore_main();

  return 0;
}
