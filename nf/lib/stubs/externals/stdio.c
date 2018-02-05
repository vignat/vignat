#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <klee/klee.h>

int
snprintf(char* str, size_t size, const char* format, ...)
{
	va_list args;
	va_start(args, format);

	// Supports only %s and single-digit %u/%d/%x, and special-cased %.2x and %.4x for 0
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
			} else if (f < len - 2 && format[f] == '.' && (format[f + 1] == '2' || format[f + 1] == '4') && format[f + 2] == 'x') {
				int format_len = format[f + 1] == '2' ? 2 : 4;
				f += 2;

				int arg = va_arg(args, int);
				klee_assert(arg == 0); // this is only used for PCI addresses

				klee_assert(size >= format_len);

				for (int n = 0; n < format_len; n++) {
					*str = '0';
					str++;
					size--;
				}
			} else {
				klee_abort(); // not supported!
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
