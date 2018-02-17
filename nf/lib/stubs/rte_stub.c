#include <rte_cpuflags.h>
#include <rte_malloc.h> // for ixgbe_rxtx

#include <ixgbe_rxtx_vec_common.h>

#include <klee/klee.h>

int
rte_cpu_get_flag_enabled(enum rte_cpu_flag_t feature)
{
	// Sentinel value - see makefile
	if (feature == (enum rte_cpu_flag_t) 424242) {
		return 1; //klee_int("rte_cpu_get_flag_enabled_return");
	}

	// Nope, not supported
	return 0;
}

const char *
rte_cpu_get_flag_name(enum rte_cpu_flag_t feature)
{
	return "<FAKE FLAG>";
}

uint64_t
get_tsc_freq_arch(void)
{
	return -1; // Not supported
}

// The implementation of ixgbe_txq_vec_setup is in a file that uses a ton of SSE ops
// but for some reason the ops it declares for ixgbe_txq_ops are just methods that
// forward to non-SSE methods... so in essence we're just copy/pasting and inlining here
static const struct ixgbe_txq_ops stub_txq_ops = {
	.release_mbufs = _ixgbe_tx_queue_release_mbufs_vec,
	.free_swring = _ixgbe_tx_free_swring_vec,
	.reset = _ixgbe_reset_tx_queue_vec
};
int
ixgbe_txq_vec_setup(struct ixgbe_tx_queue *txq)
{
	return ixgbe_txq_vec_setup_default(txq, &stub_txq_ops);
}


uint64_t
stub_rdtsc(void)
{
	uint64_t value;
	klee_make_symbolic(&value, sizeof(uint64_t), "tsc");
	return value;
}

const char *
stub_strerror(int errnum)
{
	return "<fake error description>";
}

void
stub_abort(void)
{
	klee_silent_exit(1);
}


__attribute__((constructor))
static void
stub_rte_init(void)
{
	// rte_memcpy uses fancy-schmancy intrinsics
	klee_alias_function("rte_memcpy", "memcpy");

	// rte_rdtsc uses assembly; we remain sound by modeling it as an unconstrained symbol
	// note that rte_rdtsc is static inline, so we alias it with a regex to catch all instantiations
	klee_alias_function_regex("rte_rdtsc[0-9]*", "stub_rdtsc");

	// Don't bother trying to translate error codes
	// note: this is just to avoid an snprintf, we could support it I guess...
	klee_alias_function("rte_strerror", "stub_strerror");

	// Don't let symbex die...
	klee_alias_function("abort", "stub_abort");
}
