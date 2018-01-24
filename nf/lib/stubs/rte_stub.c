#include <rte_cpuflags.h>

#include <klee/klee.h>

int
rte_cpu_get_flag_enabled(enum rte_cpu_flag_t feature)
{
	// Sentinel value - see makefile
	if (feature == (enum rte_cpu_flag_t) 424242) {
		return 1; //klee_int("rte_cpu_get_flag_enabled_return");
	}

	// Used in hash initialization
	if (feature == RTE_CPUFLAG_EM64T) {
		return 0;
	}

	klee_abort();
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


void
stub_rte_init(void)
{
	// Manually call the stack mempool initialization, since it's a constructor function
	// (which KLEE doesn't execute)
	// Except the function isn't in any header, only in the C file for stack mempools...
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wimplicit-function-declaration"
	mp_hdlr_init_ops_stack();
#pragma clang diagnostic pop

	// rte_memcpy uses fancy-schmancy intrinsics
	klee_alias_function("rte_memcpy", "memcpy");

	// Don't bother trying to translate error codes
	// note: this is just to avoid an snprintf, we could support it I guess...
	klee_alias_function("rte_strerror", "stub_strerror");

	// Don't let symbex die...
	klee_alias_function("abort", "stub_abort");
}
