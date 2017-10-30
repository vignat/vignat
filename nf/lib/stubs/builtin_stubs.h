#pragma once

#define __builtin_constant_p(x) 1

#define __sync_bool_compare_and_swap(ptr, oldval, newval) ((*ptr == oldval) ? (*ptr = newval, 1) : 0)

// DPDK only uses it as an atomic add, no fetch necessary
#define __sync_fetch_and_add(ptr, value) (*(ptr) += (value))
