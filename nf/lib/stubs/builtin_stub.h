#pragma once

#include <inttypes.h>


// Pretend we support those
#define __SSE3__
#define __SSSE3__
#define __SSE4_1__
#define __SSE4_2__


// Pretend that everything is known to be a compile-time constant, so DPDK uses less fancy tricks
#define __builtin_constant_p(x) 1


// Standard CAS (but of course we don't need atomicity)
#define __sync_bool_compare_and_swap(ptr, oldval, newval) ((*ptr == oldval) ? (*ptr = newval, 1) : 0)


// DPDK only uses it as an atomic add, no fetch necessary
// TODO make it decent anyway, we shouldn't rely on that
#define __sync_fetch_and_add(ptr, value) (*(ptr) += (value))

// idem than add, but with sub
#define __sync_fetch_and_sub(ptr, value) (*(ptr) -= (value))


// Despite it being called test_and_set, GCC docs describe it as "not a traditional test-and-set operation, but rather an atomic exchange operation"
static inline int32_t stub_test_and_set(volatile int32_t* ptr, int32_t value)
{
	int32_t prev = *ptr;
	*ptr = value;
	return prev;
}
#define __sync_lock_test_and_set stub_test_and_set
