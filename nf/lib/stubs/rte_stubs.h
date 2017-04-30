
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <netinet/in.h>

#ifndef RTE_STUBS_H
#define RTE_STUBS_H

#include "lib/custom_ether_addr_def.h"

#define IPV4_HDR_IHL_MASK 0x0f

#define TAILQ_ENTRY(type)                                               \
    struct {                                                            \
        struct type *tqe_next;  /* next element */                      \
        struct type **tqe_prev; /* address of previous next element */  \
    }

#define RTE_CACHE_LINE_SIZE 64                  /**< Cache line size. */
#define __rte_cache_aligned __attribute__((__aligned__(RTE_CACHE_LINE_SIZE)))

#define IPv4(a,b,c,d) ((uint32_t)(((a) & 0xff) << 24) | \
                       (((b) & 0xff) << 16) | \
                       (((c) & 0xff) << 8)  | \
                       ((d) & 0xff))

#define RTE_PTYPE_L3_IPV4                   0x00000010
#define  RTE_ETH_IS_IPV4_HDR(ptype) ((ptype) & RTE_PTYPE_L3_IPV4)

#define rte_pktmbuf_mtod_offset(m, t, o)    \
    ((t)((char *)(m)->buf_addr + (m)->data_off + (o)))

#define rte_pktmbuf_mtod(m, t) rte_pktmbuf_mtod_offset(m, t, 0)

typedef void    *MARKER[0];   /**< generic marker for a point in a structure */
typedef uint8_t  MARKER8[0];  /**< generic marker with 1B alignment */
typedef uint64_t MARKER64[0]; /**< marker that allows us to overwrite 8 bytes
                               * with a single assignment */
typedef uint64_t phys_addr_t; /**< Physical address definition. */

typedef struct {
    volatile int16_t cnt; /**< An internal counter value. */
} rte_atomic16_t;

struct rte_mbuf {
    MARKER cacheline0;

    void *buf_addr;           /**< Virtual address of segment buffer. */
    phys_addr_t buf_physaddr; /**< Physical address of segment buffer. */

    uint16_t buf_len;         /**< Length of segment buffer. */

    MARKER8 rearm_data;
    uint16_t data_off;

    union {
        rte_atomic16_t refcnt_atomic; /**< Atomically accessed refcnt */
        uint16_t refcnt;              /**< Non-atomically accessed refcnt */
    };
    uint8_t nb_segs;          /**< Number of segments. */
    uint8_t port;             /**< Input port. */

    uint64_t ol_flags;        /**< Offload features. */

    /* remaining bytes are set on RX when pulling packet from descriptor */
    MARKER rx_descriptor_fields1;

    union {
        uint32_t packet_type; /**< L2/L3/L4 and tunnel information. */
        struct {
            uint32_t l2_type:4; /**< (Outer) L2 type. */
            uint32_t l3_type:4; /**< (Outer) L3 type. */
            uint32_t l4_type:4; /**< (Outer) L4 type. */
            uint32_t tun_type:4; /**< Tunnel type. */
            uint32_t inner_l2_type:4; /**< Inner L2 type. */
            uint32_t inner_l3_type:4; /**< Inner L3 type. */
            uint32_t inner_l4_type:4; /**< Inner L4 type. */
        };
    };

    uint32_t pkt_len;         /**< Total pkt len: sum of all segments. */
    uint16_t data_len;        /**< Amount of data in segment buffer. */
    uint16_t vlan_tci;        /**< VLAN Tag Control Identifier (CPU order) */

    union {
            uint32_t rss;     /**< RSS hash result if RSS enabled */
        struct {
            union {
                struct {
                    uint16_t hash;
                    uint16_t id;
                };
                uint32_t lo;
                /**< Second 4 flexible bytes */
            };
            uint32_t hi;
            /**< First 4 flexible bytes or FD ID, dependent on
                 PKT_RX_FDIR_* flag in ol_flags. */
        } fdir;           /**< Filter identifier if FDIR enabled */
        uint32_t sched;   /**< Hierarchical scheduler */
        uint32_t usr;      /**< User defined tags. See rte_distributor_process() */
    } hash;                   /**< hash information */

    uint32_t seqn; /**< Sequence number. See also rte_reorder_insert() */
    uint16_t vlan_tci_outer;  /**< Outer VLAN Tag Control Identifier (CPU order) */

    /* second cache line - fields only used in slow path or on TX */
    MARKER cacheline1 __rte_cache_aligned;

    union {
        void *userdata;   /**< Can be used for external metadata */
        uint64_t udata64; /**< Allow 8-byte userdata on 32-bit */
    };

    struct rte_mempool *pool; /**< Pool from which mbuf was allocated. */
    struct rte_mbuf *next;    /**< Next segment of scattered packet. */

    /* fields to support TX offloads */
    union {
        uint64_t tx_offload;       /**< combined for easy fetch */
        struct {
            uint64_t l2_len:7; /**< L2 (MAC) Header Length. */
            uint64_t l3_len:9; /**< L3 (IP) Header Length. */
            uint64_t l4_len:8; /**< L4 (TCP/UDP) Header Length. */
            uint64_t tso_segsz:16; /**< TCP TSO segment size */

            /* fields for TX offloading of tunnels */
            uint64_t outer_l3_len:9; /**< Outer L3 (IP) Hdr Length. */
            uint64_t outer_l2_len:7; /**< Outer L2 (MAC) Hdr Length. */

            /* uint64_t unused:8; */
        };
    };

    /** Size of the application private data. In case of an indirect
     * mbuf, it stores the direct mbuf private data size. */
    uint16_t priv_size;

    /** Timesync flags for use with IEEE1588. */
    uint16_t timesync;
} __rte_cache_aligned;

struct ether_hdr {
    struct ether_addr d_addr; /**< Destination address. */
    struct ether_addr s_addr; /**< Source address. */
    uint16_t ether_type;      /**< Frame type. */
} __attribute__((__packed__));

struct ipv4_hdr {
    uint8_t  version_ihl;        /**< version and header length */
    uint8_t  type_of_service;    /**< type of service */
    uint16_t total_length;        /**< length of packet */
    uint16_t packet_id;        /**< packet ID */
    uint16_t fragment_offset;    /**< fragmentation offset */
    uint8_t  time_to_live;        /**< time to live */
    uint8_t  next_proto_id;        /**< protocol ID */
    uint16_t hdr_checksum;        /**< header checksum */
    uint32_t src_addr;        /**< source address */
    uint32_t dst_addr;        /**< destination address */
} __attribute__((__packed__));

static inline uint16_t rte_arch_bswap16(uint16_t _x)
{
    return ((_x >> 8) | ((_x << 8) & 0xff00));
}

static inline uint32_t rte_arch_bswap32(uint32_t _x)
{
    return ((_x >> 24) | ((_x >> 8) & 0xff00) | ((_x << 8) & 0xff0000) |
        ((_x << 24) & 0xff000000));
}

static inline uint64_t rte_arch_bswap64(uint64_t _x)
{
    return ((_x >> 56) | ((_x >> 40) & 0xff00) | ((_x >> 24) & 0xff0000) |
        ((_x >> 8) & 0xff000000) | ((_x << 8) & (0xffULL << 32)) |
        ((_x << 24) & (0xffULL << 40)) |
        ((_x << 40) & (0xffULL << 48)) | ((_x << 56)));
}

#define rte_cpu_to_be_16(x) rte_arch_bswap16(x)
#define rte_cpu_to_be_32(x) rte_arch_bswap32(x)
#define rte_cpu_to_be_64(x) rte_arch_bswap64(x)

#define rte_be_to_cpu_16(x) rte_arch_bswap16(x)
#define rte_be_to_cpu_32(x) rte_arch_bswap32(x)
#define rte_be_to_cpu_64(x) rte_arch_bswap64(x)

static inline uint32_t
__rte_raw_cksum(const void *buf, size_t len, uint32_t sum)
{
    /* workaround gcc strict-aliasing warning */
    uintptr_t ptr = (uintptr_t)buf;
    const uint16_t *u16 = (const uint16_t *)ptr;

    while (len >= (sizeof(*u16) * 4)) {
        sum += u16[0];
        sum += u16[1];
        sum += u16[2];
        sum += u16[3];
        len -= sizeof(*u16) * 4;
        u16 += 4;
    }
    while (len >= sizeof(*u16)) {
        sum += *u16;
        len -= sizeof(*u16);
        u16 += 1;
    }

    /* if length is in odd bytes */
    if (len == 1)
        sum += *((const uint8_t *)u16);

    return sum;
}

static inline uint16_t
__rte_raw_cksum_reduce(uint32_t sum)
{
    sum = ((sum & 0xffff0000) >> 16) + (sum & 0xffff);
    sum = ((sum & 0xffff0000) >> 16) + (sum & 0xffff);
    return (uint16_t)sum;
}

static inline uint16_t
rte_raw_cksum(const void *buf, size_t len)
{
    uint32_t sum;

    sum = __rte_raw_cksum(buf, len, 0);
    return __rte_raw_cksum_reduce(sum);
}

#define PKT_TX_TCP_SEG       (1ULL << 50)

static inline uint16_t
rte_ipv4_phdr_cksum(const struct ipv4_hdr *ipv4_hdr, uint64_t ol_flags)
{
    struct ipv4_psd_header {
        uint32_t src_addr; /* IP address of source host. */
        uint32_t dst_addr; /* IP address of destination host. */
        uint8_t  zero;     /* zero. */
        uint8_t  proto;    /* L4 protocol type. */
        uint16_t len;      /* L4 length. */
    } psd_hdr;

    psd_hdr.src_addr = ipv4_hdr->src_addr;
    psd_hdr.dst_addr = ipv4_hdr->dst_addr;
    psd_hdr.zero = 0;
    psd_hdr.proto = ipv4_hdr->next_proto_id;
    if (ol_flags & PKT_TX_TCP_SEG) {
        psd_hdr.len = 0;
    } else {
        psd_hdr.len = rte_cpu_to_be_16(
            (uint16_t)(rte_be_to_cpu_16(ipv4_hdr->total_length)
                - sizeof(struct ipv4_hdr)));
    }
    return rte_raw_cksum(&psd_hdr, sizeof(psd_hdr));
}

static inline uint16_t
rte_ipv4_cksum(const struct ipv4_hdr *ipv4_hdr)
{
    uint16_t cksum;
    cksum = rte_raw_cksum(ipv4_hdr, sizeof(struct ipv4_hdr));
    return (cksum == 0xffff) ? cksum : ~cksum;
}


static inline uint16_t
rte_ipv4_udptcp_cksum(const struct ipv4_hdr *ipv4_hdr, const void *l4_hdr)
{
    uint32_t cksum;
    uint32_t l4_len;

    l4_len = rte_be_to_cpu_16(ipv4_hdr->total_length) -
        sizeof(struct ipv4_hdr);

    cksum = rte_raw_cksum(l4_hdr, l4_len);
    cksum += rte_ipv4_phdr_cksum(ipv4_hdr, 0);

    cksum = ((cksum & 0xffff0000) >> 16) + (cksum & 0xffff);
    cksum = (~cksum) & 0xffff;
    if (cksum == 0)
        cksum = 0xffff;

    return cksum;
}

void
rte_exit(int exit_code, const char *format, ...);

static inline void ether_addr_copy(const struct ether_addr *ea_from,
                   struct ether_addr *ea_to)
{
    *ea_to = *ea_from;
}

struct rte_eth_link {
    uint16_t link_speed;      /**< ETH_LINK_SPEED_[10, 100, 1000, 10000] */
    uint16_t link_duplex;     /**< ETH_LINK_[HALF_DUPLEX, FULL_DUPLEX] */
    uint8_t  link_status : 1; /**< 1 -> link up, 0 -> link down */
}__attribute__((aligned(8)));     /**< aligned for atomic64 read/write */

struct rte_pci_resource {
    uint64_t phys_addr;   /**< Physical address, 0 if no resource. */
    uint64_t len;         /**< Length of the resource. */
    void *addr;           /**< Virtual address, NULL when not mapped. */
};

#define PCI_MAX_RESOURCE 6

struct rte_pci_id {
    uint16_t vendor_id;           /**< Vendor ID or PCI_ANY_ID. */
    uint16_t device_id;           /**< Device ID or PCI_ANY_ID. */
    uint16_t subsystem_vendor_id; /**< Subsystem vendor ID or PCI_ANY_ID. */
    uint16_t subsystem_device_id; /**< Subsystem device ID or PCI_ANY_ID. */
};

struct rte_pci_addr {
    uint16_t domain;                /**< Device domain */
    uint8_t bus;                    /**< Device bus */
    uint8_t devid;                  /**< Device ID */
    uint8_t function;               /**< Device function. */
};

enum rte_devtype {
    RTE_DEVTYPE_WHITELISTED_PCI,
    RTE_DEVTYPE_BLACKLISTED_PCI,
    RTE_DEVTYPE_VIRTUAL,
};

/**
 * Structure that stores a device given by the user with its arguments
 *
 * A user device is a physical or a virtual device given by the user to
 * the DPDK application at startup through command line arguments.
 *
 * The structure stores the configuration of the device, its PCI
 * identifier if it's a PCI device or the driver name if it's a virtual
 * device.
 */
struct rte_devargs {
    /** Next in list. */
    TAILQ_ENTRY(rte_devargs) next;
    /** Type of device. */
    enum rte_devtype type;
    union {
        /** Used if type is RTE_DEVTYPE_*_PCI. */
        struct {
            /** PCI location. */
            struct rte_pci_addr addr;
        } pci;
        /** Used if type is RTE_DEVTYPE_VIRTUAL. */
        struct {
            /** Driver name. */
            char drv_name[32];
        } virtual;
    };
    /** Arguments string as given by user or "" for no argument. */
    char *args;
};

enum rte_kernel_driver {
    RTE_KDRV_UNKNOWN = 0,
    RTE_KDRV_IGB_UIO,
    RTE_KDRV_VFIO,
    RTE_KDRV_UIO_GENERIC,
    RTE_KDRV_NIC_UIO,
};

#define RTE_MAX_RXTX_INTR_VEC_ID     32

enum rte_intr_handle_type {
    RTE_INTR_HANDLE_UNKNOWN = 0,
    RTE_INTR_HANDLE_UIO,          /**< uio device handle */
    RTE_INTR_HANDLE_UIO_INTX,     /**< uio generic handle */
    RTE_INTR_HANDLE_VFIO_LEGACY,  /**< vfio device handle (legacy) */
    RTE_INTR_HANDLE_VFIO_MSI,     /**< vfio device handle (MSI) */
    RTE_INTR_HANDLE_VFIO_MSIX,    /**< vfio device handle (MSIX) */
    RTE_INTR_HANDLE_ALARM,    /**< alarm handle */
    RTE_INTR_HANDLE_MAX
};

#define RTE_INTR_EVENT_ADD            1UL
#define RTE_INTR_EVENT_DEL            2UL

typedef void (*rte_intr_event_cb_t)(int fd, void *arg);

struct rte_epoll_data {
    uint32_t event;               /**< event type */
    void *data;                   /**< User data */
    rte_intr_event_cb_t cb_fun;   /**< IN: callback fun */
    void *cb_arg;                  /**< IN: callback arg */
};

enum {
    RTE_EPOLL_INVALID = 0,
    RTE_EPOLL_VALID,
    RTE_EPOLL_EXEC,
};

/** interrupt epoll event obj, taken by epoll_event.ptr */
struct rte_epoll_event {
    volatile uint32_t status;  /**< OUT: event status */
    int fd;                    /**< OUT: event fd */
    int epfd;       /**< OUT: epoll instance the ev associated with */
    struct rte_epoll_data epdata;
};

/** Handle for interrupts. */
struct rte_intr_handle {
    union {
        int vfio_dev_fd;  /**< VFIO device file descriptor */
        int uio_cfg_fd;  /**< UIO config file descriptor
                    for uio_pci_generic */
    };
    int fd;     /**< interrupt event file descriptor */
    enum rte_intr_handle_type type;  /**< handle type */
    uint32_t max_intr;             /**< max interrupt requested */
    uint32_t nb_efd;               /**< number of available efd(event fd) */
    int efds[RTE_MAX_RXTX_INTR_VEC_ID];  /**< intr vectors/efds mapping */
    struct rte_epoll_event elist[RTE_MAX_RXTX_INTR_VEC_ID];
                       /**< intr vector epoll event */
    int *intr_vec;                 /**< intr vector number array */
};

struct rte_pci_driver;
struct rte_pci_device;

/**
 * Initialisation function for the driver called during PCI probing.
 */
typedef int (pci_devinit_t)(struct rte_pci_driver *, struct rte_pci_device *);

/**
 * Uninitialisation function for the driver called during hotplugging.
 */
typedef int (pci_devuninit_t)(struct rte_pci_device *);

/**
 * A structure describing a PCI driver.
 */
struct rte_pci_driver {
    TAILQ_ENTRY(rte_pci_driver) next;       /**< Next in list. */
    const char *name;                       /**< Driver name. */
    pci_devinit_t *devinit;                 /**< Device init. function. */
    pci_devuninit_t *devuninit;             /**< Device uninit function. */
    const struct rte_pci_id *id_table;    /**< ID table, NULL terminated. */
    uint32_t drv_flags;                     /**< Flags contolling handling of device. */
};

/**
 * A structure describing a PCI device.
 */
struct rte_pci_device {
    TAILQ_ENTRY(rte_pci_device) next;       /**< Next probed PCI device. */
    struct rte_pci_addr addr;               /**< PCI location. */
    struct rte_pci_id id;                   /**< PCI ID. */
    struct rte_pci_resource mem_resource[PCI_MAX_RESOURCE];   /**< PCI Memory Resource */
    struct rte_intr_handle intr_handle;     /**< Interrupt handle */
    struct rte_pci_driver *driver;          /**< Associated driver */
    uint16_t max_vfs;                       /**< sriov enable if not zero */
    int numa_node;                          /**< NUMA node connection */
    struct rte_devargs *devargs;            /**< Device user arguments */
    enum rte_kernel_driver kdrv;            /**< Kernel driver passthrough */
};

struct rte_eth_thresh {
    uint8_t pthresh; /**< Ring prefetch threshold. */
    uint8_t hthresh; /**< Ring host threshold. */
    uint8_t wthresh; /**< Ring writeback threshold. */
};

struct rte_eth_rxconf {
    struct rte_eth_thresh rx_thresh; /**< RX ring threshold registers. */
    uint16_t rx_free_thresh; /**< Drives the freeing of RX descriptors. */
    uint8_t rx_drop_en; /**< Drop packets if no descriptors are available. */
    uint8_t rx_deferred_start; /**< Do not start queue with rte_eth_dev_start(). */
};

struct rte_eth_txconf {
    struct rte_eth_thresh tx_thresh; /**< TX ring threshold registers. */
    uint16_t tx_rs_thresh; /**< Drives the setting of RS bit on TXDs. */
    uint16_t tx_free_thresh; /**< Start freeing TX buffers if there are
                      less free descriptors than this value. */

    uint32_t txq_flags; /**< Set flags for the Tx queue */
    uint8_t tx_deferred_start; /**< Do not start queue with rte_eth_dev_start(). */
};

struct rte_eth_dev_info {
    struct rte_pci_device *pci_dev; /**< Device PCI information. */
    const char *driver_name; /**< Device Driver name. */
    unsigned int if_index; /**< Index to bound host interface, or 0 if none.
        Use if_indextoname() to translate into an interface name. */
    uint32_t min_rx_bufsize; /**< Minimum size of RX buffer. */
    uint32_t max_rx_pktlen; /**< Maximum configurable length of RX pkt. */
    uint16_t max_rx_queues; /**< Maximum number of RX queues. */
    uint16_t max_tx_queues; /**< Maximum number of TX queues. */
    uint32_t max_mac_addrs; /**< Maximum number of MAC addresses. */
    uint32_t max_hash_mac_addrs;
    /** Maximum number of hash MAC addresses for MTA and UTA. */
    uint16_t max_vfs; /**< Maximum number of VFs. */
    uint16_t max_vmdq_pools; /**< Maximum number of VMDq pools. */
    uint32_t rx_offload_capa; /**< Device RX offload capabilities. */
    uint32_t tx_offload_capa; /**< Device TX offload capabilities. */
    uint16_t reta_size;
    /**< Device redirection table size, the total number of entries. */
    uint8_t hash_key_size; /**< Hash key size in bytes */
    /** Bit mask of RSS offloads, the bit offset also means flow type */
    uint64_t flow_type_rss_offloads;
    struct rte_eth_rxconf default_rxconf; /**< Default RX configuration */
    struct rte_eth_txconf default_txconf; /**< Default TX configuration */
    uint16_t vmdq_queue_base; /**< First queue ID for VMDQ pools. */
    uint16_t vmdq_queue_num;  /**< Queue number for VMDQ pools. */
    uint16_t vmdq_pool_base;  /**< First ID of VMDQ pools. */
};

#define RTE_RING_NAMESIZE 32 /**< The maximum length of a ring name. */

struct rte_ring {
    char name[RTE_RING_NAMESIZE];    /**< Name of the ring. */
    int flags;                       /**< Flags supplied at creation. */

    /** Ring producer status. */
    struct prod {
        uint32_t watermark;      /**< Maximum items before EDQUOT. */
        uint32_t sp_enqueue;     /**< True, if single producer. */
        uint32_t size;           /**< Size of ring. */
        uint32_t mask;           /**< Mask (size-1) of ring. */
        volatile uint32_t head;  /**< Producer head. */
        volatile uint32_t tail;  /**< Producer tail. */
    } prod __rte_cache_aligned;

    /** Ring consumer status. */
    struct cons {
        uint32_t sc_dequeue;     /**< True, if single consumer. */
        uint32_t size;           /**< Size of the ring. */
        uint32_t mask;           /**< Mask (size-1) of ring. */
        volatile uint32_t head;  /**< Consumer head. */
        volatile uint32_t tail;  /**< Consumer tail. */
    } cons;

    void * ring[0] __rte_cache_aligned; /**< Memory space of ring starts here.
                                         * not volatile so need to be careful
                                         * about compiler re-ordering */
};

#define RTE_MEMPOOL_NAMESIZE 32 /**< Maximum length of a memory pool. */
#define    MEMPOOL_PG_NUM_DEFAULT    1

struct rte_mempool {
    char name[RTE_MEMPOOL_NAMESIZE]; /**< Name of mempool. */
    struct rte_ring *ring;           /**< Ring to store objects. */
    phys_addr_t phys_addr;           /**< Phys. addr. of mempool struct. */
    int flags;                       /**< Flags of the mempool. */
    uint32_t size;                   /**< Size of the mempool. */
    uint32_t cache_size;             /**< Size of per-lcore local cache. */
    uint32_t cache_flushthresh;
    /**< Threshold before we flush excess elements. */

    uint32_t elt_size;               /**< Size of an element. */
    uint32_t header_size;            /**< Size of header (before elt). */
    uint32_t trailer_size;           /**< Size of trailer (after elt). */

    unsigned private_data_size;      /**< Size of private data. */

    /* Address translation support, starts from next cache line. */

    /** Number of elements in the elt_pa array. */
    uint32_t    pg_num __rte_cache_aligned;
    uint32_t    pg_shift;     /**< LOG2 of the physical pages. */
    uintptr_t   pg_mask;      /**< physical page mask value. */
    uintptr_t   elt_va_start;
    /**< Virtual address of the first mempool object. */
    uintptr_t   elt_va_end;
    /**< Virtual address of the <size + 1> mempool object. */
    phys_addr_t elt_pa[MEMPOOL_PG_NUM_DEFAULT];
    /**< Array of physical page addresses for the mempool objects buffer. */

}  __rte_cache_aligned;

typedef int (lcore_function_t)(void *);

enum rte_rmt_call_master_t {
    SKIP_MASTER = 0, /**< lcore handler not executed by master core. */
    CALL_MASTER,     /**< lcore handler executed by master core. */
};

struct rte_eth_rss_conf {
    uint8_t *rss_key;    /**< If not NULL, 40-byte hash key. */
    uint8_t rss_key_len; /**< hash key length in bytes. */
    uint64_t rss_hf;     /**< Hash functions to apply - see below. */
};
#define ETH_MQ_RX_RSS_FLAG  0x1
#define ETH_MQ_RX_DCB_FLAG  0x2
#define ETH_MQ_RX_VMDQ_FLAG 0x4

/**
 *  A set of values to identify what method is to be used to route
 *  packets to multiple queues.
 */
enum rte_eth_rx_mq_mode {
    /** None of DCB,RSS or VMDQ mode */
    ETH_MQ_RX_NONE = 0,

    /** For RX side, only RSS is on */
    ETH_MQ_RX_RSS = ETH_MQ_RX_RSS_FLAG,
    /** For RX side,only DCB is on. */
    ETH_MQ_RX_DCB = ETH_MQ_RX_DCB_FLAG,
    /** Both DCB and RSS enable */
    ETH_MQ_RX_DCB_RSS = ETH_MQ_RX_RSS_FLAG | ETH_MQ_RX_DCB_FLAG,

    /** Only VMDQ, no RSS nor DCB */
    ETH_MQ_RX_VMDQ_ONLY = ETH_MQ_RX_VMDQ_FLAG,
    /** RSS mode with VMDQ */
    ETH_MQ_RX_VMDQ_RSS = ETH_MQ_RX_RSS_FLAG | ETH_MQ_RX_VMDQ_FLAG,
    /** Use VMDQ+DCB to route traffic to queues */
    ETH_MQ_RX_VMDQ_DCB = ETH_MQ_RX_VMDQ_FLAG | ETH_MQ_RX_DCB_FLAG,
    /** Enable both VMDQ and DCB in VMDq */
    ETH_MQ_RX_VMDQ_DCB_RSS = ETH_MQ_RX_RSS_FLAG | ETH_MQ_RX_DCB_FLAG |
                 ETH_MQ_RX_VMDQ_FLAG,
};

struct rte_eth_rxmode {
    /** The multi-queue packet distribution mode to be used, e.g. RSS. */
    enum rte_eth_rx_mq_mode mq_mode;
    uint32_t max_rx_pkt_len;  /**< Only used if jumbo_frame enabled. */
    uint16_t split_hdr_size;  /**< hdr buf size (header_split enabled).*/
    uint16_t header_split : 1, /**< Header Split enable. */
        hw_ip_checksum   : 1, /**< IP/UDP/TCP checksum offload enable. */
        hw_vlan_filter   : 1, /**< VLAN filter enable. */
        hw_vlan_strip    : 1, /**< VLAN strip enable. */
        hw_vlan_extend   : 1, /**< Extended VLAN enable. */
        jumbo_frame      : 1, /**< Jumbo Frame Receipt enable. */
        hw_strip_crc     : 1, /**< Enable CRC stripping by hardware. */
        enable_scatter   : 1, /**< Enable scatter packets rx handler */
        enable_lro       : 1; /**< Enable LRO */
};

enum rte_eth_tx_mq_mode {
    ETH_MQ_TX_NONE    = 0,  /**< It is in neither DCB nor VT mode. */
    ETH_MQ_TX_DCB,          /**< For TX side,only DCB is on. */
    ETH_MQ_TX_VMDQ_DCB,    /**< For TX side,both DCB and VT is on. */
    ETH_MQ_TX_VMDQ_ONLY,    /**< Only VT on, no DCB */
};

struct rte_eth_txmode {
    enum rte_eth_tx_mq_mode mq_mode; /**< TX multi-queues mode. */

    /* For i40e specifically */
    uint16_t pvid;
    uint8_t hw_vlan_reject_tagged : 1,
        /**< If set, reject sending out tagged pkts */
        hw_vlan_reject_untagged : 1,
        /**< If set, reject sending out untagged pkts */
        hw_vlan_insert_pvid : 1;
        /**< If set, enable port based VLAN insertion */
};

struct rte_eth_conf {
    /* just relevant fields: */
    struct rte_eth_rxmode rxmode;
    struct {
        struct rte_eth_rss_conf rss_conf; /**< Port RSS configuration */
    } rx_adv_conf;
    struct rte_eth_txmode txmode;
    /* ... and many many many more, but unrelevant */
};

#define RTE_MAX_ETHPORTS 32

#define ETHER_TYPE_IPv4 0x0800 /**< IPv4 Protocol. */

struct tcp_hdr {
    uint16_t src_port;  /**< TCP source port. */
    uint16_t dst_port;  /**< TCP destination port. */
    uint32_t sent_seq;  /**< TX data sequence number. */
    uint32_t recv_ack;  /**< RX data acknowledgement sequence number. */
    uint8_t  data_off;  /**< Data offset. */
    uint8_t  tcp_flags; /**< TCP flags */
    uint16_t rx_win;    /**< RX flow control window. */
    uint16_t cksum;     /**< TCP checksum. */
    uint16_t tcp_urp;   /**< TCP urgent pointer, if any. */
} __attribute__((__packed__));

struct udp_hdr {
    uint16_t src_port;    /**< UDP source port. */
    uint16_t dst_port;    /**< UDP destination port. */
    uint16_t dgram_len;   /**< UDP datagram length */
    uint16_t dgram_cksum; /**< UDP datagram checksum */
} __attribute__((__packed__));

#define US_PER_MS 1000
#define MS_PER_S 1000
#define US_PER_S (US_PER_MS * MS_PER_S)

#define ETHER_MAX_LEN   1518  /**< Maximum frame len, including CRC. */
#define ETHER_ADDR_FMT_SIZE         18

#define RTE_PKTMBUF_HEADROOM 128
#define    RTE_MBUF_DEFAULT_DATAROOM    2048
#define    RTE_MBUF_DEFAULT_BUF_SIZE    \
    (RTE_MBUF_DEFAULT_DATAROOM + RTE_PKTMBUF_HEADROOM)

#define ETH_LINK_FULL_DUPLEX    2       /**< Full-duplex connection. */

static inline void
ether_format_addr(char *buf, uint16_t size,
          const struct ether_addr *eth_addr)
{
    sprintf(buf, "%02X:%02X:%02X:%02X:%02X:%02X",
         eth_addr->addr_bytes[0],
         eth_addr->addr_bytes[1],
         eth_addr->addr_bytes[2],
         eth_addr->addr_bytes[3],
         eth_addr->addr_bytes[4],
         eth_addr->addr_bytes[5]);
}

#define RTE_MAX(a, b) ({ \
        typeof (a) _a = (a); \
        typeof (b) _b = (b); \
        _a > _b ? _a : _b; \
    })

#define RTE_ETH_FLOW_UNKNOWN             0
#define RTE_ETH_FLOW_RAW                 1
#define RTE_ETH_FLOW_IPV4                2
#define RTE_ETH_FLOW_FRAG_IPV4           3
#define RTE_ETH_FLOW_NONFRAG_IPV4_TCP    4
#define RTE_ETH_FLOW_NONFRAG_IPV4_UDP    5
#define RTE_ETH_FLOW_NONFRAG_IPV4_SCTP   6
#define RTE_ETH_FLOW_NONFRAG_IPV4_OTHER  7
#define RTE_ETH_FLOW_IPV6                8
#define RTE_ETH_FLOW_FRAG_IPV6           9
#define RTE_ETH_FLOW_NONFRAG_IPV6_TCP   10
#define RTE_ETH_FLOW_NONFRAG_IPV6_UDP   11
#define RTE_ETH_FLOW_NONFRAG_IPV6_SCTP  12
#define RTE_ETH_FLOW_NONFRAG_IPV6_OTHER 13
#define RTE_ETH_FLOW_L2_PAYLOAD         14
#define RTE_ETH_FLOW_IPV6_EX            15
#define RTE_ETH_FLOW_IPV6_TCP_EX        16
#define RTE_ETH_FLOW_IPV6_UDP_EX        17
#define RTE_ETH_FLOW_MAX                18

#define ETH_RSS_IPV4               (1ULL << RTE_ETH_FLOW_IPV4)
#define ETH_RSS_FRAG_IPV4          (1ULL << RTE_ETH_FLOW_FRAG_IPV4)
#define ETH_RSS_NONFRAG_IPV4_TCP   (1ULL << RTE_ETH_FLOW_NONFRAG_IPV4_TCP)
#define ETH_RSS_NONFRAG_IPV4_UDP   (1ULL << RTE_ETH_FLOW_NONFRAG_IPV4_UDP)
#define ETH_RSS_NONFRAG_IPV4_SCTP  (1ULL << RTE_ETH_FLOW_NONFRAG_IPV4_SCTP)
#define ETH_RSS_NONFRAG_IPV4_OTHER (1ULL << RTE_ETH_FLOW_NONFRAG_IPV4_OTHER)
#define ETH_RSS_IPV6               (1ULL << RTE_ETH_FLOW_IPV6)
#define ETH_RSS_FRAG_IPV6          (1ULL << RTE_ETH_FLOW_FRAG_IPV6)
#define ETH_RSS_NONFRAG_IPV6_TCP   (1ULL << RTE_ETH_FLOW_NONFRAG_IPV6_TCP)
#define ETH_RSS_NONFRAG_IPV6_UDP   (1ULL << RTE_ETH_FLOW_NONFRAG_IPV6_UDP)
#define ETH_RSS_NONFRAG_IPV6_SCTP  (1ULL << RTE_ETH_FLOW_NONFRAG_IPV6_SCTP)
#define ETH_RSS_NONFRAG_IPV6_OTHER (1ULL << RTE_ETH_FLOW_NONFRAG_IPV6_OTHER)
#define ETH_RSS_L2_PAYLOAD         (1ULL << RTE_ETH_FLOW_L2_PAYLOAD)
#define ETH_RSS_IPV6_EX            (1ULL << RTE_ETH_FLOW_IPV6_EX)
#define ETH_RSS_IPV6_TCP_EX        (1ULL << RTE_ETH_FLOW_IPV6_TCP_EX)
#define ETH_RSS_IPV6_UDP_EX        (1ULL << RTE_ETH_FLOW_IPV6_UDP_EX)

#define ETH_RSS_IP (                                    \
                    ETH_RSS_IPV4 |                      \
                    ETH_RSS_FRAG_IPV4 |                 \
                    ETH_RSS_NONFRAG_IPV4_OTHER |        \
                    ETH_RSS_IPV6 |                      \
                    ETH_RSS_FRAG_IPV6 |                 \
                    ETH_RSS_NONFRAG_IPV6_OTHER |        \
                    ETH_RSS_IPV6_EX)

#define RTE_LCORE_FOREACH_SLAVE(i)                               \
  for (i = rte_get_closest_next_lcore(0, 1, 0);                  \
       i<RTE_MAX_LCORE;                                          \
       i = rte_get_closest_next_lcore(i+1, 1, 0))

#define unlikely(x) (x)

#define RTE_MAX_LCORE 128

int rte_lcore_is_enabled(unsigned lcore_id);
unsigned rte_get_master_lcore();

static inline unsigned
rte_get_closest_next_lcore(unsigned i, int skip_master, int wrap)
{
    if (wrap)
        i %= RTE_MAX_LCORE;

    while (i < RTE_MAX_LCORE) {
        if (!rte_lcore_is_enabled(i) ||
            (skip_master && (i == rte_get_master_lcore()))) {
            i++;
            if (wrap)
                i %= RTE_MAX_LCORE;
            continue;
        }
        break;
    }
    return i;
}


struct user_buf {
  //uint8_t some_data[100];
  struct ether_hdr ether;
  struct ipv4_hdr ipv4;
  struct tcp_hdr tcp;
};
// Below goes gutted rte functions.


uint16_t rte_eth_tx_burst(uint8_t port, uint16_t queueid, struct rte_mbuf **tx_pkts, uint16_t n);
void flood(struct rte_mbuf* frame,
           uint8_t skip_device,
           uint8_t nb_devices);
void rte_pktmbuf_free(struct rte_mbuf *mbufp);
uint64_t rte_get_tsc_hz();
unsigned rte_lcore_id();
uint64_t rte_rdtsc();
uint16_t rte_eth_rx_burst(uint8_t portid, uint8_t queueid, struct rte_mbuf** pkts_burst, int max_burst);
void rte_prefetch0(const volatile void *p);
int rte_lcore_is_enabled(unsigned lcore_id);
unsigned rte_lcore_to_socket_id(unsigned lcore_id);
unsigned rte_socket_id(void);
unsigned rte_eth_dev_socket_id(uint8_t device);
void rte_eth_link_get_nowait(uint8_t portid, struct rte_eth_link* link);
void rte_delay_ms(unsigned ms);
int rte_eal_init(int argc, char ** argv);
uint8_t rte_eth_dev_count();
uint8_t rte_lcore_count();
int rte_eth_dev_configure(uint8_t portid, uint16_t nb_rx_queue, uint16_t nb_tx_queue, struct rte_eth_conf * port_conf);
void rte_eth_macaddr_get(uint8_t portid, struct ether_addr *addr);
void rte_eth_dev_info_get(uint8_t portid, struct rte_eth_dev_info *info);
int rte_eth_tx_queue_setup(uint8_t portid, uint16_t queueid, uint16_t nb_tx_desc, unsigned int socketid, struct rte_eth_txconf* txconf);
int rte_eth_rx_queue_setup(uint8_t portid, uint16_t queueid, uint16_t nb_rxd, unsigned int socketid, struct rte_eth_rxconf *rxconf, struct rte_mempool *mpool);
int rte_eth_dev_start(uint8_t portid);
void rte_eth_promiscuous_enable(uint8_t portid);
int rte_eal_mp_remote_launch(lcore_function_t *f, void* arg, enum rte_rmt_call_master_t call_master);
int rte_eal_wait_lcore(unsigned lcore_id);
struct rte_mempool *
rte_pktmbuf_pool_create(const char *name, unsigned n,
                        unsigned cache_size, uint16_t priv_size, uint16_t data_room_size,
                        int socket_id);
unsigned rte_get_master_lcore();
const char* rte_strerror(int errnum);
struct rte_mbuf* rte_pktmbuf_clone(struct rte_mbuf *md,
                                   struct rte_mempool *mp);
extern int rte_errno;

#endif //RTE_STUBS_H
