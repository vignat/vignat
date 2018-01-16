#include <pthread.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>

#include <sys/syscall.h>

#include <klee/klee.h>


// Common values
static const char* CPU_ID_PATH_FORMAT = "/sys/devices/system/cpu/cpu%u/topology/core_id";
static const char* CPU_ID_VALUE_ZERO = "/sys/devices/system/cpu/cpu0/topology/core_id";


// Useful macros
#define LENGTH(str) (sizeof(str)/sizeof(str[0]))


// Helper methods that do not use libc methods
bool
fake_strcmp(const char* left, const char* right)
{
	int l, r;
        for (l = 0, r = 0; left[l] && right[r]; l++, r++) { }
        return !left[l] && !right[r];
}

void
fake_strcpy(char* dst, const char* src)
{
	int n;
	for (n = 0; src[n]; n++) {
		dst[n] = src[n];
	}
	dst[n] = '\0';
}


int
snprintf(char* str, size_t size, const char* format, ...)
{
	va_list args;
	va_start(args, format);

	// If DPDK can't find any of the CPU files, it fails, so let's say CPU 0 exists
	if (fake_strcmp(format, CPU_ID_PATH_FORMAT) && size >= LENGTH(CPU_ID_VALUE_ZERO)) {
		if (va_arg(args, unsigned) == 0) {
			fake_strcpy(str, CPU_ID_VALUE_ZERO);
			return LENGTH(CPU_ID_VALUE_ZERO) - 1;; // not including null terminator
		}
	}

	// snprintf is allowed to return 0 if it fails (e.g. no memory)
	// So we return 0 unless we really need to
	return 0;
}

int
vfprintf(FILE* stream, const char* format, _G_va_list __arg)
{
	// TODO FIXME
	return 0;
}

pthread_t
pthread_self(void)
{
	// We are on CPU 0 - always
	return 0;
}

int
pthread_setaffinity_np(pthread_t thread, size_t cpusetsize, const cpu_set_t* cpuset)
{
	// Not supported
	return -1;
}


FILE*
fopencookie(void* cookie, const char* mode, cookie_io_functions_t io_funcs)
{
	FILE* f = (FILE*) malloc(sizeof(FILE));;
	klee_forbid_access(f, sizeof(FILE), "fopencookie");
	return f;
}

int
access(const char* pathname, int mode)
{
	// Yup, CPU 0 exists!
	if (fake_strcmp(pathname, CPU_ID_VALUE_ZERO) && mode == F_OK) {
		return 0;
	}

	return -1;
}

int
open(const char* path, int oflags)
{
	// Nope, can't open, sorry!
	return -1;
}

int
timerfd_create(int clockid, int flags)
{
	// OK, its usage implies timerfd_gettime/settime and we don't support those
	// so we know the app doesn't actually need a timer
	return 0;
}

int
clock_gettime(clockid_t clk_id, struct timespec* tp)
{
	// Not supported!
	return -1;
}

unsigned int
sleep(unsigned int seconds)
{
	// Whatever, code shouldn't use sleep anyway
	// If this exposes bugs, great!
	return 0;
}

long
syscall(long number, ...)
{
	// 0 sounds ridiculous, 1 is init, so let's say 2
	if (number == SYS_gettid) {
		return 2;
	}

	// Not supported!
	return -1;
}
