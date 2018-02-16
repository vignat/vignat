#pragma once

#include <unistd.h>

#define STUB_FILES_COUNT 1024

// note: we only support 1 pipe
#define STUB_PIPE_FD_READ (STUB_FILES_COUNT + 1)
#define STUB_PIPE_FD_WRITE (STUB_FILES_COUNT + 2)

void stub_pipe_write(const void* buf, size_t len);
