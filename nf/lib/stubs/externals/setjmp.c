#include <setjmp.h>

int
sigsetjmp(sigjmp_buf env, int savesigs)
{
	// We don't support longjmp, so nothing to do here

	// setjmp() and sigsetjmp() return 0 if returning directly, and nonzero when returning from longjmp(3) or siglongjmp(3) using the saved context.
	// -- https://linux.die.net/man/3/sigsetjmp
	return 0;
}
