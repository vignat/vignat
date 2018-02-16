#include "lib/stubs/externals/externals_stub.h"
#include "lib/stubs/hardware_stub.h"

// GNU_SOURCE for fopencookie (TODO define here, not on compile line)
//#define _GNU_SOURCE
#include <stdio.h>
//#undef _GNU_SOURCE

#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <klee/klee.h>

int
snprintf(char* str, size_t size, const char* format, ...)
{
	va_list args;
	va_start(args, format);

	// Supports only %s and single-digit %u/%d/%x, and %[0|.][2|4][x|X]
	size_t orig_size = size;
	int len = strlen(format);
	for (int f = 0; f < len; f++) {
		if (format[f] == '%') {
			klee_assert(f < len - 1);

			f++;
			if (format[f] == 's') {
				char* arg = va_arg(args, char*);
				int arg_len = strlen(arg);

				klee_assert(size >= arg_len);

				strcpy(str, arg);
				str += arg_len;
				size -= arg_len;
			} else if (format[f] == 'u') {
				unsigned arg = va_arg(args, unsigned);
				if (arg > 10) {
					return -1; // not supported! - TODO but dpdk needs it anyway, fix it...
				}

				klee_assert(size >= 1);

				*str = '0';
				for (int n = 0; n < arg; n++) {
					*str = *str + 1;
				}

				str++;
				size--;
			} else if (format[f] == 'd' || format[f] == 'x') {
				int arg = va_arg(args, int);
				klee_assert(arg < 10); // we only support single digits (thus base doesn't matter)

				klee_assert(size >= 1);

				*str = '0';
				for (int n = 0; n < arg; n++) {
					*str = *str + 1;
				}

				str++;
				size--;
			} else {
				if (f < len && format[f] == '.') {
					// Ignore the dot; we only support 'x'/'X' with small enough numbers,
					// so the difference between precision and width doesn't matter
					f++;
				}

				if (f < len && format[f] == '0') {
					// Zero-padding is the only behavior we support anyway
					f++;
				}

				// This code probably works with any number 1-9 in format[f]...
				// could probably even be merged into the other 'x' support
				if (f < len - 1
					&& (format[f] == '2' || format[f] == '4')
					&& (format[f + 1] == 'x' || format[f + 1] == 'X')) {
					int format_len = format[f] == '2' ? 2 : 4;
					bool uppercase = format[f + 1] == 'X';
					f++;

					int arg = va_arg(args, int);
					klee_assert(arg < (1 << (4 * format_len))); // make sure the number doesn't overflow

					klee_assert(size >= format_len);

					for (int n = format_len - 1; n >= 0; n--) {
						int digit = arg % 16;
						arg = arg / 16;

						if (digit < 10) {
							*str = '0' + digit;
						} else if (uppercase) {
							*str = 'A' + (digit - 10);
						} else {
							*str = 'a' + (digit - 10);
						}

						str++;
						size--;
					}
				} else {
					klee_abort(); // not supported!
				}
			}
		} else {
			if (size < 1) {
				klee_abort(); // too small!
			}

			*str = format[f];
			str++;
			size--;
		}
	}

	if (size < 1) {
		klee_abort(); // too small!
	}

	*str = '\0';
	// no size-- here, return value does not include null terminator

	return orig_size - size;
}

int
vfprintf(FILE* stream, const char* format, _G_va_list __arg)
{
	klee_assert(stream == stderr);

	return 0; // OK, whatever
}

int
vprintf(const char *format, va_list arg)
{
	return 0; // OK, whatever, we don't care about stdout
}

FILE*
fopencookie(void* cookie, const char* mode, cookie_io_functions_t io_funcs)
{
	FILE* f = (FILE*) malloc(sizeof(FILE));;
	klee_forbid_access(f, sizeof(FILE), "fopencookie");
	return f;
}

// We implement this here since it's common to multiple kinds of I/O: files and pipes
ssize_t
write(int fd, const void* buf, size_t count)
{
	// http://man7.org/linux/man-pages/man2/write.2.html

	// "According to POSIX.1, if count is greater than SSIZE_MAX, the result is implementation-defined"
	klee_assert(count <= SSIZE_MAX);

	// "On Linux, write() (and similar system calls) will transfer at most 0x7ffff000 (2,147,479,552) bytes,
	//  returning the number of bytes actually transferred."
	klee_assert(count <= 0x7ffff000);

	// Either we write to the stub pipe, or to an interrupt file
	if (fd == STUB_PIPE_FD_WRITE) {
		stub_pipe_write(buf, count);
	} else {
		klee_assert(count == 4);

		for (int n = 0; n < sizeof(DEVICES)/sizeof(DEVICES[0]); n++) {
			if (fd == DEVICES[n].interrupts_fd) {
				if (*((uint32_t*) buf) == 0) {
					DEVICES[n].interrupts_enabled = false;
				} else if (*((uint32_t*) buf) == 1) {
					DEVICES[n].interrupts_enabled = true;
				} else {
					klee_abort();
				}

				goto success;
			}
		}

		klee_abort();
	}

	// "On success, the number of bytes written is returned (zero indicates nothing was written).
	//  It is not an error if this number is smaller than the number of bytes requested."
success:
	return 0;
}
