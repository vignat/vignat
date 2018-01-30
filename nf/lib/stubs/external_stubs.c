#include <dirent.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>

#include <klee/klee.h>


// Common constants
// TODO: We pretend CPU 0 / NUMA node 0 exist, but what about others?
static const char* CPU_ID_PATH_FORMAT = "/sys/devices/system/cpu/cpu%u/topology/core_id";
static const char* CPU_ID_VALUE_ZERO = "/sys/devices/system/cpu/cpu0/topology/core_id";
static const char* CPU_PATH_FORMAT = "/sys/devices/system/cpu/cpu%u/%s";
static const char* CPU_ID_PATH = "topology/core_id";

static const char* NUMA_PATH_FORMAT = "%s/node%u/cpu%u";
static const char* NUMA_PATH_PREFIX = "/sys/devices/system/node";
static const char* NUMA_VALUE_ZERO = "/sys/devices/system/node/node0/cpu0";

static const int PCI_DEVICES_COUNT = 2;
static const char* PCI_DEVICE_NAMES[] = { "0000:00:00.0", "0000:00:00.1" };
static const char* PCI_FILE_PREFIX = "/sys/bus/pci/devices/";


// Globals
// TODO this is kind of hacky - we should have some kind of "symbol that is never equal to anything"
static int CPU_ID_ZERO_FD = 42;
static ssize_t CPU_ID_ZERO_FD_READ_BYTES = 0;

static int PCI_DIR_FD = 4242;
static int PCI_DIR_FD_READ_ENTRIES = 0;

struct stub_pci_file {
	int fd;
	const char* name;
	int pos; // -2 == past EOF, -1 == unopened, >=0 == current pos
	const char* content;
};
static struct stub_pci_file PCI_FILES[] = {
	{ .fd = 42000, .name = "vendor", .pos = -1, .content = "32902\n" }, // value: ixgbe
	{ .fd = 42001, .name = "device", .pos = -1, .content = "5546\n" }, // value: ixgbe
	{ .fd = 42002, .name = "subsystem_vendor", .pos = -1, .content = "0\n" }, // value: any
	{ .fd = 42003, .name = "subsystem_device", .pos = -1, .content = "0\n" }, // value: any
	{ .fd = 42004, .name = "class", .pos = -1, .content = "16777215\n" }, // value: ixgbe
	{ .fd = 42005, .name = "max_vfs", .pos = -1, .content = "0\n" }, // no virtual functions
	{ .fd = 42006, .name = "numa_node", .pos = -1, .content = "0\n" }, // NUMA node 0
	{ .fd = 42007, .name = "resource", .pos = -1, .content =
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n" }, // idk what this is
};


int
snprintf(char* str, size_t size, const char* format, ...)
{
	// NOTE: return value is length, but not including null terminator

	va_list args;
	va_start(args, format);

	// CPU ID for CPU 0
	if (!strcmp(format, CPU_ID_PATH_FORMAT)) {
		unsigned core = va_arg(args, unsigned);
		if (core == 0 && size >= strlen(CPU_ID_VALUE_ZERO)) {
			strcpy(str, CPU_ID_VALUE_ZERO);
			return strlen(CPU_ID_VALUE_ZERO);
		}

		return -1; // TODO support it
	}

	// Same, but for some reason the second part is a %s as well
	// TODO: If we end up upstreaming DPDK patches, might as well do this...
	if (!strcmp(format, CPU_PATH_FORMAT)) {
		if (va_arg(args, unsigned) == 0 && strlen(CPU_ID_VALUE_ZERO) < size) {
			if (!strcmp(va_arg(args, char*), CPU_ID_PATH)) {
				strcpy(str, CPU_ID_VALUE_ZERO);
				return strlen(CPU_ID_VALUE_ZERO);
			}
		}
	}

	// NUMA node 0, CPU 0
	if (!strcmp(format, NUMA_PATH_FORMAT)) {
		if (!strcmp(va_arg(args, char*), NUMA_PATH_PREFIX)) {
			unsigned socket = va_arg(args, unsigned);
			unsigned core = va_arg(args, unsigned);
			if (socket == 0 && core == 0 && strlen(NUMA_VALUE_ZERO) < size) {
				strcpy(str, NUMA_VALUE_ZERO);
				return strlen(NUMA_VALUE_ZERO);
			}

			return -1; // TODO not supported yet
		}
	}

	// CPU 0 with a comma, when dumping affinity
	if (!strcmp(format, "%u,")) {
		unsigned arg = va_arg(args, unsigned);
		if (arg == 0) {
			const char* result = "0,";
			if (strlen(result) < size) {
				strcpy(str, result);
				return strlen(result);
			}
		}
	}

	// Memory pool name
	if (!strcmp(format, "MP_%s")) {
		char* name = va_arg(args, char*);
		if (name != NULL && strlen(name) + 3 < size) {
			strcpy(str, "MP_");
			str += 3;
			strcpy(str, name);
			return strlen(name) + 3;
		}
	}

	// Memory pool sub-name
	if (!strcmp(format, "MP_%s_%d")) {
		char* name = va_arg(args, char*);
		if (name != NULL) {
			// NOTE: this is a DPDK bug, format should be %u...
			unsigned id = va_arg(args, unsigned);
			if (strlen(name) + 5 < size) {
				strcpy(str, "MP_");
				str += 3;

				strcpy(str, name);

				if (id == 0) {
					strcpy(str, "_0");
				} else if (id == 2) {
					strcpy(str, "_2");
				} else {
					klee_abort();
				}

				return strlen(name) + 5;
			}
		}
	}

	// Path-like format
	if (!strcmp(format, "%s/%s")) {
		char* arg0 = va_arg(args, char*);
		char* arg1 = va_arg(args, char*);
		if (arg0 == NULL || arg1 == NULL || strlen(arg0) + 1 + strlen(arg1) >= size) {
			klee_abort();
		}

		strcpy(str, arg0);
		str += strlen(arg0);
		str[0] = '/';
		str++;
		strcpy(str, arg1);

		return strlen(arg0) + 1 + strlen(arg1);
	}

	// String, then suffix (the observant reader will notice this doesn't handle %% - I don't care)
	if (strlen(format) > 2 && format[0] == '%' && format[1] == 's') {
		bool has_percent = false;
		for (int n = 2; n < strlen(format); n++) {
			has_percent |= format[n] == '%';
		}
		if (!has_percent) {
			char* arg = va_arg(args, char*);
			if (strlen(arg) + (strlen(format) - 2) <= size) {
				strcpy(str, arg);
				str += strlen(arg);
				format += 2;
				strcpy(str, format);
				return strlen(arg) + strlen(format); // not len(format)-2 cause we just += 2
			}
		}
	}

	// Trivial case: string copy
	if (!strcmp(format, "%s")) {
		char* arg = va_arg(args, char*);
		if (arg != NULL) {
			if (strlen(arg) <= size) {
				strcpy(str, arg);
				return strlen(arg) - 1;
			}
		}
	}


	if (!strcmp(format, "%.4" PRIx16 ":%.2" PRIx8 ":%.2" PRIx8 ".%" PRIx8)) {
		uint32_t domain = va_arg(args, uint32_t);
		uint8_t bus = va_arg(args, int);
		uint8_t devid = va_arg(args, int);
		uint8_t function = va_arg(args, int);

		if (domain == 0 && bus == 0 && devid == 0) {
			strcpy(str, PCI_DEVICE_NAMES[function]);
			return strlen(PCI_DEVICE_NAMES[function]);
		}
	}

	klee_abort();
}

int
access(const char* pathname, int mode)
{
	// Yup, CPU 0 exists!
	if (!strcmp(pathname, CPU_ID_VALUE_ZERO) && mode == F_OK) {
		return 0;
	}

	// CPU 0 on NUMA node 0 exists too!
	if (!strcmp(pathname, NUMA_VALUE_ZERO) && mode == F_OK) {
		return 0;
	}

	// Yes, /sys stuff is accessible
	if (strlen(pathname) > 5 && pathname[0] == '/' && pathname[1] == 's' && pathname[2] == 'y' && pathname[3] == 's' && pathname[4] == '/') {
		return 0;
	}

	klee_abort();
}

int
stat(const char* path, struct stat* buf)
{
	// Nope, we don't have modules
	if (!strcmp(path, "/sys/module")) {
		return -1;
	}

	klee_abort();
}

int
fstat(int fd, struct stat* buf)
{
	if (fd == PCI_DIR_FD) {
		memset(buf, 0, sizeof(struct stat));
		return 0;
	}

	klee_abort();
}

int
fcntl(int fd, int cmd, ...)
{
        va_list args;
        va_start(args, cmd);

	if (fd == PCI_DIR_FD && cmd == F_SETFD) {
		int arg = va_arg(args, int);
		if (arg == FD_CLOEXEC) {
			return 0;
		}
	}

	klee_abort();
}

int
open(const char* file, int oflag, ...)
{
	// CPU 0
	if (!strcmp(file, CPU_ID_VALUE_ZERO) && oflag == O_RDONLY) {
		return CPU_ID_ZERO_FD;
	}

	// page map
	if (!strcmp(file, "/proc/self/pagemap") && oflag == O_RDONLY) {
		return -1; // TODO
	}

	// cpu info
	if (!strcmp(file, "/proc/cpuinfo") && oflag == O_RDONLY) {
		return -1; // TODO
	}

	// PCI devices
	if (!strcmp(file, "/sys/bus/pci/devices") && oflag == (O_RDONLY|O_NDELAY|O_DIRECTORY)) {
		return PCI_DIR_FD;
	}

	// PCI devices info
	if (!strncmp(file, PCI_FILE_PREFIX, strlen(PCI_FILE_PREFIX))) {
		int skip_len = strlen(PCI_FILE_PREFIX) // path suffix
				+ strlen(PCI_DEVICE_NAMES[0]) // actual name
				+ 1; // trailing slash
		if (strlen(file) > skip_len) {
			file += skip_len;

			for (int n = 0; n < sizeof(PCI_FILES)/sizeof(PCI_FILES[0]); n++) {
				if (!strcmp(file, PCI_FILES[n].name)) {
					PCI_FILES[n].pos = 0;
					return PCI_FILES[n].fd;
				}
			}
		}
	}

	// Not supported!
	klee_abort();
}

ssize_t
read(int fd, void *buf, size_t count)
{
	if (fd == CPU_ID_ZERO_FD && count == 1) {
		if (CPU_ID_ZERO_FD_READ_BYTES == 0) {
			*((char*) buf) = '0';
			return 1;
		}
	}

	if (count == 1) {
		for (int n = 0; n < sizeof(PCI_FILES)/sizeof(PCI_FILES[0]); n++) {
			if (fd == PCI_FILES[n].fd) {
				if (PCI_FILES[n].pos == -1) {
					klee_abort(); // not opened!
				} else if (PCI_FILES[n].pos == -2) {
					klee_abort(); // past EOF!
				} else if (PCI_FILES[n].pos < strlen(PCI_FILES[n].content)) {
					*((char*) buf) = PCI_FILES[n].content[PCI_FILES[n].pos];
					PCI_FILES[n].pos++;
					return 1;
				} else {
					PCI_FILES[n].pos = -2;
					return 0;
				}
			}
		}
	}

	// Not supported!
	klee_abort();
}

int
close(int fd)
{
	// TODO: set FDs to -1 so they won't work any more unless re-opened - assume a single fd in flight at any time

	if (fd == CPU_ID_ZERO_FD) {
//		CPU_ID_ZERO_FD = -1;
		return 0;
	}

	if (fd == PCI_DIR_FD) {
//		PCI_DIR_FD = -1;
		return 0;
	}

	for (int n = 0; n < sizeof(PCI_FILES)/sizeof(PCI_FILES[0]); n++) {
		if (fd == PCI_FILES[n].fd) {
			PCI_FILES[n].pos = -1;
			return 0;
		}
	}

	// Not supported!
	klee_abort();
}

ssize_t
readlink(const char* pathname, char* buf, size_t bufsiz)
{
	if (!strncmp(pathname, PCI_FILE_PREFIX, strlen(PCI_FILE_PREFIX))) {
		int skip_len = strlen(PCI_FILE_PREFIX) // path suffix
				+ strlen(PCI_DEVICE_NAMES[0]) // actual name
				+ 1; // trailing slash
                if (strlen(pathname) > skip_len) {
			pathname += skip_len;
			if (!strcmp(pathname, "driver")) {
				// Dirname doesn't matter to DPDK, only filename
				// TODO can we make it a symbol of sorts? what about returning -1?
				const char* driver_path = "/drivers/igb_uio";
				klee_assert(strlen(driver_path) < bufsiz);
				strcpy(buf, driver_path);
				return strlen(driver_path);
			}
		}
	}

	klee_abort();
}

// NOTE: This is a klee-uclibc internal
//       which is excluded from build because other stuff next to it causes problems with klee
//       according to a comment in libc/Makefile.in
//       The gist of it is that it reads N directory entries,
//       with a limit on the number of bytes, and returns the number of bytes actually read.
ssize_t
__getdents (int fd, char* buf, size_t nbytes)
{
	if (fd == PCI_DIR_FD) {
		if (PCI_DIR_FD_READ_ENTRIES >= PCI_DEVICES_COUNT) {
			return 0;
		}

		size_t len = sizeof(struct dirent);
		if (nbytes < len) {
			klee_abort();
		}

		struct dirent* de = (struct dirent*) buf;
		memset(de, 0, len);

		de->d_ino = 1; // just needs to be non-zero
		strcpy(de->d_name, PCI_DEVICE_NAMES[PCI_DIR_FD_READ_ENTRIES]);
		de->d_reclen = strlen(de->d_name);

		PCI_DIR_FD_READ_ENTRIES++;

		return len;
	}

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

int
vprintf(const char *format, va_list arg)
{
	return 0; // OK, whatever, we don't care about stdout
}

pthread_t
pthread_self(void)
{
	// We are on CPU 0 - always
	return 0;
}

int
pthread_getaffinity_np(pthread_t thread, size_t cpusetsize, cpu_set_t* cpuset)
{
	// We're running in a symbolic executor. the concept of "affinity" is meaningless
	int ret = klee_int("pthread_getaffinity_np_return");

	// However, we might be given uninitialized memory, so we need to set it
	if (ret >= 0) {
		// TODO all bits should be symbols...
		CPU_ZERO(cpuset);
		CPU_SET(0, cpuset);
	}

	return ret;
}


int
pthread_setaffinity_np(pthread_t thread, size_t cpusetsize, const cpu_set_t* cpuset)
{
	// Same remark as getaffinity
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

void*
mmap(void* addr, size_t length, int prot, int flags, int fd, off_t offset)
{
	// We support a single mapping
	if (addr == NULL) {
		// With read/write pages (otherwise it's messy to handle)
		if (prot & (PROT_READ | PROT_WRITE)) {
			// and only anonymous and private
			if (flags == (MAP_PRIVATE | MAP_ANONYMOUS)) {
				// http://man7.org/linux/man-pages/man2/mmap.2.html
				// The mapping is not backed by any file; its contents are initialized to zero.
				// The fd argument is ignored; however, some implementations require fd to be -1
				// if MAP_ANONYMOUS is specified, and portable applications should ensure this.
				// The offset argument should be zero.
				klee_assert(fd == -1);
				klee_assert(offset == 0);

				void* mem = malloc(length);
				memset(mem, 0, length);
				return mem;
			}
		}
	}

	klee_abort();
}



// FIXME LLVM uses intrinsics for memmove so we can't use the uclibc one for some reason
//       (i.e its declaration is not linked in with the rest like e.g. strcmp)
//       so for now we just copy/paste it from uclibc...
void*
memmove(void* s1, const void* s2, size_t n)
{
        char* s = (char*) s1;
        const char* p = (const char*) s2;

        if (p >= s) {
                while (n) {
                        *s++ = *p++;
                        --n;
                }
        } else {
                while (n) {
                        --n;
                        s[n] = p[n];
                }
        }

        return s1;
}
