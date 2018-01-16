#include <fcntl.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>

#include <sys/syscall.h>

#include <klee/klee.h>


// Common values
// TODO: We pretend CPU 0 / NUMA node 0 exist, but what about others?
static const char* CPU_ID_PATH_FORMAT = "/sys/devices/system/cpu/cpu%u/topology/core_id";
static const char* CPU_ID_VALUE_ZERO = "/sys/devices/system/cpu/cpu0/topology/core_id";
static const char* CPU_PATH_FORMAT = "/sys/devices/system/cpu/cpu%u/%s";
static const char* CPU_ID_PATH = "topology/core_id";

static int CPU_ID_ZERO_FD;
static ssize_t CPU_ID_ZERO_FD_READ_BYTES = 0;

static const char* NUMA_PATH_FORMAT = "%s/node%u/cpu%u";
static const char* NUMA_PATH_PREFIX = "/sys/devices/system/node";
static const char* NUMA_VALUE_ZERO = "/sys/devices/system/node/node0/cpu0";

static const char* PAGEMAP_PATH = "/proc/self/pagemap";

static const char* CPUINFO_PATH = "/proc/cpuinfo";

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
	// NOTE: return value is length, but not including null terminator

	va_list args;
	va_start(args, format);

	// CPU ID for CPU 0
	if (fake_strcmp(format, CPU_ID_PATH_FORMAT)) {
		unsigned core = va_arg(args, unsigned);
		if (core == 0 && size >= LENGTH(CPU_ID_VALUE_ZERO)) {
			fake_strcpy(str, CPU_ID_VALUE_ZERO);
			return LENGTH(CPU_ID_VALUE_ZERO) - 1;
		}

		return -1; // TODO support it
	}

	// Same, but for some reason the second part is a %s as well
	// TODO: If we end up upstreaming DPDK patches, might as well do this...
	if (fake_strcmp(format, CPU_PATH_FORMAT)) {
		if (va_arg(args, unsigned) == 0 && size >= LENGTH(CPU_ID_VALUE_ZERO)) {
			if (fake_strcmp(va_arg(args, char*), CPU_ID_PATH)) {
				fake_strcpy(str, CPU_ID_VALUE_ZERO);
				return LENGTH(CPU_ID_VALUE_ZERO) - 1;
			}
		}
	}

	// NUMA node 0, CPU 0
	if (fake_strcmp(format, NUMA_PATH_FORMAT)) {
		if (fake_strcmp(va_arg(args, char*), NUMA_PATH_PREFIX)) {
			unsigned socket = va_arg(args, unsigned);
			unsigned core = va_arg(args, unsigned);
			if (socket == 0 && core == 0 && size >= LENGTH(NUMA_VALUE_ZERO)) {
				fake_strcpy(str, NUMA_VALUE_ZERO);
				return LENGTH(NUMA_VALUE_ZERO) - 1;
			}

			return -1; // TODO not supported yet
		}
	}

	// CPU 0 with a comma, when dumping affinity
	if (fake_strcmp(format, "%u,")) {
		unsigned arg = va_arg(args, unsigned);
		if (arg == 0) {
			const char* result = "0,";
			if (size >= LENGTH(result)) {
				fake_strcpy(str, result);
				return LENGTH(result) - 1;
			}
		}
	}

	// Memory pool name
	if (fake_strcmp(format, "MP_%s")) {
		char* name = va_arg(args, char*);
		if (name != NULL && LENGTH(name) + 3 <= size) {
			fake_strcpy(str, "MP_");
			str += 3;
			fake_strcpy(str, name);
			return LENGTH(name) + 3 - 1;
		}
	}

	// Memory pool sub-name
	if (fake_strcmp(format, "MP_%s_%d")) {
		char* name = va_arg(args, char*);
		if (name != NULL) {
			// NOTE: this is a DPDK bug, format should be %u...
			unsigned id = va_arg(args, unsigned);
			if (LENGTH(name) + 5 <= size) {
				fake_strcpy(str, "MP_");
				str += 3;

				fake_strcpy(str, name);

				if (id == 0) {
					fake_strcpy(str, "_0");
				} else if (id == 2) {
					fake_strcpy(str, "_2");
				} else {
					klee_abort();
				}

				return LENGTH(name) + 5 - 1;
			}
		}
	}

	// Trivial case: string copy
	if (fake_strcmp(format, "%s")) {
		char* arg = va_arg(args, char*);
		if (arg != NULL) {
			if (LENGTH(arg) <= size) {
				fake_strcpy(str, arg);
				return LENGTH(arg) - 1;
			}
		}
	}

	// snprintf is allowed to return 0 if it fails (e.g. no memory)
	// So we return 0 unless we really need to
	klee_abort();
}

int
vfprintf(FILE* stream, const char* format, _G_va_list __arg)
{
	if (stream == stderr) {
		return 0; // OK, whatever
	}

	// Not supported
	klee_abort();
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
	// We're running in a symbolic executor anyway, the concept of "affinity" is meaningless...
	return klee_int("pthread_setaffinity_np_return");
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

	// CPU 0 on NUMA node 0 exists too!
	if (fake_strcmp(pathname, NUMA_VALUE_ZERO) && mode == F_OK) {
		return 0;
	}

	klee_abort();
}

int
open(const char* file, int oflag, ...)
{
	// CPU 0
	if (fake_strcmp(file, CPU_ID_VALUE_ZERO) && oflag == O_RDONLY) {
		if (!klee_is_symbolic(CPU_ID_ZERO_FD)) {
			CPU_ID_ZERO_FD = klee_int("cpu_id_zero_fd");
		}
		return CPU_ID_ZERO_FD;
	}

	// page map
	if (fake_strcmp(file, PAGEMAP_PATH) && oflag == O_RDONLY) {
		return -1; // TODO
	}

	if (fake_strcmp(file, CPUINFO_PATH) && oflag == O_RDONLY) {
		return -1; // TODO
	}

	// Not supported!
	klee_abort();
}

ssize_t
read(int fd, void *buf, size_t count)
{
	if(fd == CPU_ID_ZERO_FD) {
		if (count == 1) {
			if (CPU_ID_ZERO_FD_READ_BYTES == 0) {
				*((char*) buf) = '0';
				return 1;
			}
			klee_print_expr("read_bytes", CPU_ID_ZERO_FD_READ_BYTES);
		}
		klee_print_expr("count", count);
	}

	// Not supported!
	klee_abort();
}

int
close(int fd)
{
	if (fd == CPU_ID_ZERO_FD) {
		// the FD won't work any more unless it's opened again
		CPU_ID_ZERO_FD = -1;
		return 0;
	}

	// Not supported!
	klee_abort();
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
