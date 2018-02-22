#include <fnmatch.h>
#include <string.h>

#include <klee/klee.h>

int
fnmatch(const char *pattern, const char *string, int flags)
{
	if (!strcmp(pattern, "*map_*") && !strcmp(string, ".") && flags == 0) {
		// Return value:
		// Zero if string matches pattern, FNM_NOMATCH if there is no match or
		// another nonzero value if there is an error.
		// -- http://man7.org/linux/man-pages/man3/fnmatch.3.html
		return FNM_NOMATCH;
	}

	klee_abort();
}
