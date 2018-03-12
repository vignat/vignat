#pragma once

#include <inttypes.h>


inline uint16_t
rte_eth_dev_count(void)
{
	return 2;
}

struct rte_eth_link {
	uint32_t link_speed;
	uint16_t link_duplex  : 1;
	uint16_t link_autoneg : 1;
	uint16_t link_status  : 1;
};

struct rte_eth_conf {
/*	uint32_t link_speeds;
	struct rte_eth_rxmode rxmode;
	struct rte_eth_txmode txmode;
	uint32_t lpbk_mode;
	struct {
		struct rte_eth_rss_conf rss_conf;
		struct rte_eth_vmdq_dcb_conf vmdq_dcb_conf;
		struct rte_eth_dcb_rx_conf dcb_rx_conf;
		struct rte_eth_vmdq_rx_conf vmdq_rx_conf;
	} rx_adv_conf;
	union {
		struct rte_eth_vmdq_dcb_tx_conf vmdq_dcb_tx_conf;
		struct rte_eth_dcb_tx_conf dcb_tx_conf;
		struct rte_eth_vmdq_tx_conf vmdq_tx_conf;
	} tx_adv_conf;
	uint32_t dcb_capability_en;
	struct rte_fdir_conf fdir_conf;
	struct rte_intr_conf intr_conf;*/
};
