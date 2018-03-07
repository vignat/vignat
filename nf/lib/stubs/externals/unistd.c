#include "lib/stubs/externals/externals_stub.h"

#include <signal.h>
#include <unistd.h>

#include <sys/syscall.h>
#include <sys/types.h>

#include <klee/klee.h>

unsigned int
sleep(unsigned int seconds)
{
	// Whatever, code shouldn't use sleep anyway
	// If this exposes bugs, great!
	return 0;
}

uid_t
getuid(void)
{
	// No errors: "These functions are always successful." -- http://man7.org/linux/man-pages/man2/getuid.2.html
	return 0; // We are root! well, we pretend to be, at least
}

long
syscall(long number, ...)
{
	// 0 is a kernel thing, 1 is init, so let's say 2
	if (number == SYS_gettid) {
		return 2;
	}

	// Not supported!
	klee_abort();
}

int
getpagesize(void)
{
	return PAGE_SIZE;
}

int
__syscall_rt_sigaction(int signum, const struct sigaction *act,
			struct sigaction *oldact, size_t _something) {
	// We don't support signals, so no need to do anything

	// sigaction() returns 0 on success; on error, -1 is returned, and errno is set to indicate the error.
	// -- http://man7.org/linux/man-pages/man2/sigaction.2.html
	return 0;
}
