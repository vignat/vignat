// NOTE: The name of this file is because if it's just called "socket.c", KLEE ignores it (even if explicitly included in the Makefile)
//       Not sure why...

#include <errno.h>
#include <stdio.h>
#include <sys/socket.h>

#include <klee/klee.h>


int
stub_socket(int family, int type, int protocol)
{
	// "On success, a file descriptor for the new socket is returned.  On error, -1 is returned, and errno is set appropriately."
	// -- http://man7.org/linux/man-pages/man2/socket.2.html
	errno = EAFNOSUPPORT; // "The implementation does not support the specified address family."
	return -1;
}


__attribute__((constructor))
static void
stub_socket_init(void)
{
	klee_alias_function("socket", "stub_socket");
}
