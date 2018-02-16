#include "lib/stubs/externals/externals_stub.h"

#include <stdbool.h>
#include <unistd.h>

#include <klee/klee.h>


static bool pipe_created = false;

int
pipe(int pipefd[2])
{
	// http://man7.org/linux/man-pages/man2/pipe.2.html

	klee_assert(!pipe_created);
	pipe_created = true;

	// "The array pipefd is used to return two file descriptors referring to the ends of the pipe.
	//  pipefd[0] refers to the read end of the pipe.
	//  pipefd[1] refers to the write end of the pipe."
	pipefd[0] = STUB_PIPE_FD_READ;
	pipefd[1] = STUB_PIPE_FD_WRITE;

	// "On success, zero is returned.  On error, -1 is returned, and errno is set appropriately."
	return 0;
}


void
stub_pipe_write(const void* buf, size_t len)
{
	// TODO for now, nothing, let's see who reads
}
