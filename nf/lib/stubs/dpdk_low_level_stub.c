#include <rte_cpuflags.h>
#include <rte_log.h>
#include <rte_malloc.h> // for ixgbe_rxtx

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


uint64_t
stub_rdtsc(void)
{
	uint64_t value;
	klee_make_symbolic(&value, sizeof(uint64_t), "tsc");
	return value;
}

void
stub_prefetch(const volatile void* p)
{
	// Nothing
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

	// rte_prefetch* functions use assembly, obviously
	klee_alias_function_regex("rte_prefetch.*", "stub_prefetch");

	// Don't bother trying to translate error codes
	// note: this is just to avoid an snprintf, we could support it I guess...
	klee_alias_function("rte_strerror", "stub_strerror");

	// Don't let symbex die...
	klee_alias_function("abort", "stub_abort");

	// Use stderr for logs
	rte_openlog_stream(stderr);
}
