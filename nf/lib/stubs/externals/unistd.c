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
	//return klee_int("page_size"); // TODO - but it propagates a symbol in annoying places
	return 4096;
}

// sigaction is implemented in klee-uclibc as a forward to a syscall, but it's easier to stub it directly
int
stub_sigaction(int signum, const struct sigaction *act, struct sigaction *oldact)
{
	// Signals aren't supported, just return success

	// sigaction() returns 0 on success; on error, -1 is returned, and errno is set to indicate the error.
	// -- http://man7.org/linux/man-pages/man2/sigaction.2.html
	return 0;
}


__attribute__((constructor))
static void
stub_unistd_init(void)
{
	klee_alias_function("sigaction", "stub_sigaction");
}
