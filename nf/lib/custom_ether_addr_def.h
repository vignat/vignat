#ifndef _CUSTOM_ETHER_ADDR_DEF_H_INCLUDED_
#define _CUSTOM_ETHER_ADDR_DEF_H_INCLUDED_

#include <stdint.h>
#include "include_ignored_by_verifast.h"
#ifdef _NO_VERIFAST_

#  ifdef KLEE_VERIFICATION

#    define ETHER_ADDR_LEN  6 /**< Length of Ethernet address. */
    struct ether_addr {
      uint8_t addr_bytes[ETHER_ADDR_LEN]; /**< Address bytes in transmission order */
    } __attribute__((__packed__));

#  else//KLEE_VERIFICATION
#    include <rte_ethdev.h>
#  endif//KLEE_VERIFICATION

#else//_NO_VERIFAST_

struct ether_addr {
  uint8_t a;
  uint8_t b;
  uint8_t c;
  uint8_t d;
  uint8_t e;
  uint8_t f;
};

#endif//_NO_VERIFAST_

#endif// _CUSTOM_ETHER_ADDR_DEF_H_INCLUDED_
