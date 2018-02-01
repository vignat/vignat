#include <dirent.h>
#include <endian.h>
#include <fcntl.h>
#include <fnmatch.h>
#include <numa.h>
#include <numaif.h>
#include <pthread.h>
#include <setjmp.h>
#include <signal.h>
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
#include <sys/types.h>

#include <klee/klee.h>

// Common constants
// TODO: We pretend CPU 0 / NUMA node 0 exist, but what about others?
static const char* CPU_ID_VALUE_ZERO = "/sys/devices/system/cpu/cpu0/topology/core_id";

static const int PCI_DEVICES_COUNT = 2;
static const char* PCI_DEVICE_NAMES[] = { "0000:00:00.0", "0000:00:00.1" };
static const char* PCI_FILE_PREFIX = "/sys/bus/pci/devices/";


// Globals
// TODO this is kind of hacky - we should have some kind of "symbol that is never equal to anything" for the FDs
static bool NUMA_INITIALIZED = false;
static bool NUMA_NODEMASK_CREATED = false;

static int CPU_ID_ZERO_FD = 69000;
static ssize_t CPU_ID_ZERO_FD_READ_BYTES = 0;

static int HUGEPAGES_DIR_FD = 69001;
static int HUGEPAGES_DIR_READ_ENTRIES = -1;

static int HUGEPAGES_MOUNTPOINT_DIR_FD = 69002;
static int HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES = -1;
static int HUGEPAGES_MOUNTPOINT_FILE_FD = 69003;
static bool HUGEPAGES_MOUNTPOINT_FILE_LOCKED = false;

#define HUGEPAGES_MMAP_COUNT 2
static void* HUGEPAGES_MMAPPED_MEM[HUGEPAGES_MMAP_COUNT] = { NULL, NULL };
static size_t HUGEPAGES_MMAPPED_SIZE[HUGEPAGES_MMAP_COUNT] = { -1, -1 };

static int HUGEPAGE_FD = 69004;
static int HUGEPAGE_ZERO_FD = 69005;

static int HUGEPAGE_INFO_FD = 69006;
static size_t HUGEPAGE_INFO_SIZE = -1;
static void* HUGEPAGE_INFO_MMAPPED_MEM = NULL;

static int PAGEMAP_FD = 69007;

static int DEV_ZERO_FD = 69010;
static void* DEV_ZERO_MMAPPED_MEM = NULL;
static size_t DEV_ZERO_MMAPPED_SIZE = -1;

static int PCI_DIR_FD = 69020;
static int PCI_DIR_READ_ENTRIES = -1;

static int PCI_UIO_DIR_FD = 69021;
static int PCI_UIO_DIR_READ_ENTRIES = -1;

static int DEV_UIO0_FD = 69100;

static int DEV_UIO0_CONFIG_FD = 69101;

struct stub_file {
	int fd;
	bool pci; // if true, name refers to a file inside a pci info
	const char* name;
	int pos; // -2 == past EOF, -1 == unopened, >=0 == current pos
	const char* content;
};

static struct stub_file KNOWN_FILES[] = {
	{ .fd = 42000, .pci = true, .name = "vendor", .pos = -1, .content = "32902\n" }, // value: ixgbe
	{ .fd = 42001, .pci = true, .name = "device", .pos = -1, .content = "5546\n" }, // value: ixgbe
	{ .fd = 42002, .pci = true, .name = "subsystem_vendor", .pos = -1, .content = "0\n" }, // value: any
	{ .fd = 42003, .pci = true, .name = "subsystem_device", .pos = -1, .content = "0\n" }, // value: any
	{ .fd = 42004, .pci = true, .name = "class", .pos = -1, .content = "16777215\n" }, // value: ixgbe
	{ .fd = 42005, .pci = true, .name = "max_vfs", .pos = -1, .content = "0\n" }, // no virtual functions
	{ .fd = 42006, .pci = true, .name = "numa_node", .pos = -1, .content = "0\n" }, // NUMA node 0
	{ .fd = 42007, .pci = true, .name = "resource", .pos = -1, .content =
		//        phys addr           end addr              flags (flag 0x200 == mem)
		"0x0000000000000000 0x0000000000000000 0x0000000000000200\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
		"0x0000000000000000 0x0000000000000000 0x0000000000000000\n" }, // one single resource

	{ .fd = 43000, .pci = false, .name = "/proc/mounts", .pos = -1,
	  .content = "hugetlbfs /dev/hugepages hugetlbfs rw,relatime 0 0\n" }, // only hugepages, what DPDK cares about
	{ .fd = 43001, .pci = false, .name = "/proc/meminfo", .pos = -1,
	  .content = "Hugepagesize:       2048 kB\n" }, // only hugepages, what DPDK cares about
	{ .fd = 43002, .pci = false, .name = "/sys/kernel/mm/hugepages/hugepages-2048kB/resv_hugepages", .pos = -1,
	  .content = "0\n" }, // reserved hugepages
	{ .fd = 43003, .pci = false, .name = "/sys/kernel/mm/hugepages/hugepages-2048kB/free_hugepages", .pos = -1,
	  .content = "1\n" }, // free hugepages
};


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
access(const char* pathname, int mode)
{
	// Yup, CPU 0 exists!
	if (!strcmp(pathname, CPU_ID_VALUE_ZERO) && mode == F_OK) {
		return 0;
	}

	// CPU 0 on NUMA node 0 exists too!
	if (!strcmp(pathname, "/sys/devices/system/node/node0/cpu0") && mode == F_OK) {
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
open(const char* file, int oflag, ...)
{
	// CPU 0
	if (!strcmp(file, CPU_ID_VALUE_ZERO) && oflag == O_RDONLY) {
		return CPU_ID_ZERO_FD;
	}

	// Other CPUs
	const char* cpu_prefix = "/sys/devices/system/cpu/cpu";
	if (!strncmp(file, cpu_prefix, strlen(cpu_prefix)) && oflag == O_RDONLY) {
		return -1; // TODO
	}

	if (!strcmp(file, "/proc/cpuinfo") && oflag == O_RDONLY) {
		return -1; // TODO
	}

	// page map
	if (!strcmp(file, "/proc/self/pagemap") && oflag == O_RDONLY) {
		return PAGEMAP_FD;
	}

	// all hugepages directory
	if (!strcmp(file, "/sys/kernel/mm/hugepages") && oflag == (O_RDONLY|O_NDELAY|O_DIRECTORY)) {
		klee_assert(HUGEPAGES_DIR_READ_ENTRIES < 0 );
		HUGEPAGES_DIR_READ_ENTRIES = 0;
		return HUGEPAGES_DIR_FD;
	}

	// hugepages directory (but sometimes opened like a file)
	if (!strcmp(file, "/dev/hugepages")) {
		if (oflag == (O_RDONLY|O_NDELAY|O_DIRECTORY)) {
			klee_assert(HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES < 0);
			HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES = 0;
			return HUGEPAGES_MOUNTPOINT_DIR_FD;
		}

		if (oflag == O_RDONLY) {
			return HUGEPAGES_MOUNTPOINT_FILE_FD;
		}
	}

	// hugepage
	if (!strcmp(file, "/dev/hugepages/rte") && oflag == (O_CREAT|O_RDWR)) {
		return HUGEPAGE_FD;
	}

	// hugepage, another
	if (!strcmp(file, "/dev/hugepages/rtemap_0") && oflag == (O_CREAT|O_RDWR)) {
		return HUGEPAGE_ZERO_FD;
	}

	// hugepage info file
	if (!strcmp(file, "/var/run/.rte_hugepage_info") && oflag == (O_CREAT|O_RDWR)) {
		HUGEPAGE_INFO_SIZE = -1;
		return HUGEPAGE_INFO_FD;
	}

	// NUMA map, unsupported for now
	// TODO support it
	if (!strcmp(file, "/proc/self/numa_maps") && oflag == O_RDONLY) {
		return -1;
	}

	// bunch of zeroes
	if (!strcmp(file, "/dev/zero") && oflag == O_RDONLY) {
		return DEV_ZERO_FD;
	}

	// UIO device
	if (!strcmp(file, "/dev/uio0") && oflag == O_RDWR) {
		return DEV_UIO0_FD;
	}

	if (!strcmp(file, "/sys/class/uio/uio0/device/config") && oflag == O_RDWR) {
		return DEV_UIO0_CONFIG_FD;
	}

	// known non-PCI files
	for (int n = 0; n < sizeof(KNOWN_FILES)/sizeof(KNOWN_FILES[0]); n++) {
		if (!KNOWN_FILES[n].pci && !strcmp(file, KNOWN_FILES[n].name)) {
			klee_assert(KNOWN_FILES[n].pos < 0);
			KNOWN_FILES[n].pos = 0;
			return KNOWN_FILES[n].fd;
		}
	}

	// PCI devices
	if (!strcmp(file, "/sys/bus/pci/devices") && oflag == (O_RDONLY|O_NDELAY|O_DIRECTORY)) {
		klee_assert(PCI_DIR_READ_ENTRIES < 0);
		PCI_DIR_READ_ENTRIES = 0;
		return PCI_DIR_FD;
	}

	// PCI devices info
	if (!strncmp(file, PCI_FILE_PREFIX, strlen(PCI_FILE_PREFIX))) {
		int skip_len = strlen(PCI_FILE_PREFIX) // path suffix
				+ strlen(PCI_DEVICE_NAMES[0]) // actual name
				+ 1; // trailing slash
		if (strlen(file) > skip_len) {
			file += skip_len;

			if (!strcmp(file, "uio") && oflag == (O_RDONLY|O_NDELAY|O_DIRECTORY)) {
				klee_assert(PCI_UIO_DIR_READ_ENTRIES < 0);
				PCI_UIO_DIR_READ_ENTRIES = 0;
				return PCI_UIO_DIR_FD;
			}

			for (int n = 0; n < sizeof(KNOWN_FILES)/sizeof(KNOWN_FILES[0]); n++) {
				if (KNOWN_FILES[n].pci && !strcmp(file, KNOWN_FILES[n].name)) {
					klee_assert(KNOWN_FILES[n].pos < 0);
					KNOWN_FILES[n].pos = 0;
					return KNOWN_FILES[n].fd;
				}
			}
		}
	}

for(int n = 0;n<strlen(file);n++){klee_print_expr("x", file[n]);}
	// Not supported!
	klee_abort();
}

int
fcntl(int fd, int cmd, ...)
{
        va_list args;
        va_start(args, cmd);

	klee_assert(cmd == F_SETFD);

	int arg = va_arg(args, int);
	klee_assert(arg == FD_CLOEXEC);

	if (fd == HUGEPAGES_DIR_FD
	 || fd == HUGEPAGES_MOUNTPOINT_DIR_FD
	 || fd == PCI_DIR_FD
	 || fd == PCI_UIO_DIR_FD) {
		return 0;
	}

	klee_abort();
}

int
flock(int fd, int operation)
{
	if (fd == HUGEPAGES_MOUNTPOINT_FILE_FD) {
		if (operation == LOCK_EX) {
			klee_assert(!HUGEPAGES_MOUNTPOINT_FILE_LOCKED);
			HUGEPAGES_MOUNTPOINT_FILE_LOCKED = true;
			return 0;
		}
		if (operation == LOCK_UN) {
			klee_assert(HUGEPAGES_MOUNTPOINT_FILE_LOCKED);
			HUGEPAGES_MOUNTPOINT_FILE_LOCKED = false;
			return 0;
		}
	}

	if ((fd == HUGEPAGE_FD || fd == HUGEPAGE_ZERO_FD) && operation == (LOCK_SH|LOCK_NB)) {
		// OK, whatever, it's a shared lock
		return 0;
	}

	klee_abort();
}

int
fstat(int fd, struct stat* buf)
{
	memset(buf, 0, sizeof(struct stat));

	if (fd == HUGEPAGES_DIR_FD
	 || fd == HUGEPAGES_MOUNTPOINT_DIR_FD
	 || fd == PCI_DIR_FD
	 || fd == PCI_UIO_DIR_FD) {
		return 0;
	}

	klee_abort();
}

int
ftruncate(int fd, off_t length)
{
	if (fd == HUGEPAGE_INFO_FD) {
		HUGEPAGE_INFO_SIZE = length;

		// On success, zero is returned. On error, -1 is returned, and errno is set appropriately.
		// -- https://linux.die.net/man/2/ftruncate
		return 0;
	}

	klee_abort();
}

off_t
lseek(int fd, off_t offset, int whence)
{
	if (fd == PAGEMAP_FD && whence == SEEK_SET) {
		// We pretend the seek was successful - pagemap always returns the same value in our stub

		// Upon successful completion, lseek() returns the resulting offset
		// location as measured in bytes from the beginning of the file. On
		// error, the value (off_t) -1 is returned and errno is set to indicate the error.
		// -- http://man7.org/linux/man-pages/man2/lseek.2.html
		return offset;
	}

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

	if (fd == PAGEMAP_FD && count == 8) {
		// Read fake pagemap data
		memset(buf, 0, count);

		// According to https://www.kernel.org/doc/Documentation/vm/pagemap.txt,
		// all we need is a non-null PFN (bits 0-54)
		// TODO I think DPDK forgets to check whether the page is marked as swapped,
		//      which changes the meaning of bits 0-54...
#if __BYTE_ORDER == __BIG_ENDIAN
		*((char*) buf + 7) = 1;
#else
		*((char*) buf) = 1;
#endif

		return count;
	}

	if (count == 1) {
		for (int n = 0; n < sizeof(KNOWN_FILES)/sizeof(KNOWN_FILES[0]); n++) {
			if (fd == KNOWN_FILES[n].fd) {
				if (KNOWN_FILES[n].pos == -1) {
					klee_abort(); // not opened!
				} else if (KNOWN_FILES[n].pos == -2) {
					klee_abort(); // past EOF!
				} else if (KNOWN_FILES[n].pos < strlen(KNOWN_FILES[n].content)) {
					*((char*) buf) = KNOWN_FILES[n].content[KNOWN_FILES[n].pos];
					KNOWN_FILES[n].pos++;
					return 1;
				} else {
					KNOWN_FILES[n].pos = -2;
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
	// TODO: change FDs so they won't work any more unless re-opened - assume a single fd in flight at any time

	if (fd == CPU_ID_ZERO_FD) {
//		CPU_ID_ZERO_FD = -1;
		return 0;
	}

	if (fd == HUGEPAGES_DIR_FD) {
		klee_assert(HUGEPAGES_DIR_READ_ENTRIES != -1);
		HUGEPAGES_DIR_READ_ENTRIES = -1;
		return 0;
	}

	if (fd == HUGEPAGES_MOUNTPOINT_DIR_FD) {
		klee_assert(HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES != -1);
		HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES = -1;
		return 0;
	}

	if (fd == HUGEPAGE_FD) {
//		HUGEPAGE_FD = -1;
		return 0;
	}

	if (fd == HUGEPAGE_ZERO_FD) {
//		HUGEPAGE_ZERO_FD = -1;
		return 0;
	}

	if (fd == HUGEPAGE_INFO_FD) {
//		HUGEPAGE_INFO_FD = -1;
		return 0;
	}

	if (fd == HUGEPAGES_MOUNTPOINT_FILE_FD) {
		klee_assert(!HUGEPAGES_MOUNTPOINT_FILE_LOCKED);
//		HUGEPAGES_MOUNTPOINT_FILE_FD = -1;
		return 0;
	}

	if (fd == PAGEMAP_FD) {
//		PAGEMAP_FD = -1;
		return 0;
	}

	if (fd == DEV_ZERO_FD) {
//		DEV_ZERO_FD = -1;
		return 0;
	}

	if (fd == PCI_DIR_FD) {
		klee_assert(PCI_DIR_READ_ENTRIES != -1);
		PCI_DIR_READ_ENTRIES = -1;
		return 0;
	}

	if (fd == PCI_UIO_DIR_FD) {
		klee_assert(PCI_UIO_DIR_READ_ENTRIES != -1);
		PCI_UIO_DIR_READ_ENTRIES = -1;
		return 0;
	}


	for (int n = 0; n < sizeof(KNOWN_FILES)/sizeof(KNOWN_FILES[0]); n++) {
		if (fd == KNOWN_FILES[n].fd) {
			klee_assert(KNOWN_FILES[n].pos != -1);
			KNOWN_FILES[n].pos = -1;
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
// NOTE: It seems that klee-uclibc is wrong
//       There is a comment 'Am I right?' in the source of readdir.c
//       However, r_reclen is not the record length but the length of the name;
//       thus, if the name is smaller than the size of struct dirent, things go wrong
//       As a workaround, we always set d_reclen to sizeof(struct dirent)...
ssize_t
__getdents (int fd, char* buf, size_t nbytes)
{
	size_t len = sizeof(struct dirent);
	klee_assert(nbytes >= len);

	struct dirent* de = (struct dirent*) buf;
	memset(de, 0, len);
	de->d_ino = 1; // just needs to be non-zero

	if (fd == HUGEPAGES_DIR_FD) {
		klee_assert(HUGEPAGES_DIR_READ_ENTRIES >= 0);

		if (HUGEPAGES_DIR_READ_ENTRIES == 1) {
			HUGEPAGES_DIR_READ_ENTRIES = -2;
			return 0;
		}

		const char* entry_name = "hugepages-2048kB";
		strcpy(de->d_name, entry_name);
		de->d_reclen = len; // strlen(de->d_name);

		HUGEPAGES_DIR_READ_ENTRIES++;

		return len;
	}

	if (fd == HUGEPAGES_MOUNTPOINT_DIR_FD) {
		klee_assert(HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES >= 0);

		if (HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES == 1) {
			HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES = -2;
			return 0;
		}

		// Empty except for '.' (which DPDK relies on...)
		de->d_name[0] = '.';
		de->d_name[1] = '\0';
		de->d_reclen = len; //1;

		HUGEPAGES_MOUNTPOINT_DIR_READ_ENTRIES++;

		return len;
	}

	if (fd == PCI_DIR_FD) {
		klee_assert(PCI_DIR_READ_ENTRIES >= 0);

		if (PCI_DIR_READ_ENTRIES >= PCI_DEVICES_COUNT) {
			PCI_DIR_READ_ENTRIES = -2;
			return 0;
		}

		strcpy(de->d_name, PCI_DEVICE_NAMES[PCI_DIR_READ_ENTRIES]);
		de->d_reclen = len; //strlen(de->d_name);

		PCI_DIR_READ_ENTRIES++;

		return len;
	}

	if (fd == PCI_UIO_DIR_FD) {
		klee_assert(PCI_UIO_DIR_READ_ENTRIES >= 0);

		if (PCI_UIO_DIR_READ_ENTRIES > 0) {
			PCI_UIO_DIR_READ_ENTRIES = -2;
			return 0;
		}

		strcpy(de->d_name, "uio0");
		de->d_reclen = len; // strlen(de->d_name);
		de->d_type = DT_DIR; // it's a directory

		PCI_UIO_DIR_READ_ENTRIES++;

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

int
numa_available(void)
{
	// Before any other calls in this library can be used numa_available() must be called.
	// If it returns -1, all other functions in this library are undefined.
	NUMA_INITIALIZED = true;
	return 0;
}

struct bitmask*
numa_allocate_nodemask()
{
	klee_assert(NUMA_INITIALIZED);

	klee_assert(!NUMA_NODEMASK_CREATED);
	NUMA_NODEMASK_CREATED = true;

	struct bitmask* mask = (struct bitmask*) malloc(sizeof(struct bitmask));
	// The bitmask is zero-filled.
	// -- https://linux.die.net/man/3/numa_alloc_onnode
	memset(mask, 0, sizeof(struct bitmask));
	return mask;
}

void
numa_bitmask_free(struct bitmask *bmp)
{
	klee_assert(NUMA_INITIALIZED);

	// It is an error to attempt to free this bitmask twice.
	// --https://linux.die.net/man/3/numa_alloc_onnode
	klee_assert(NUMA_NODEMASK_CREATED);
	NUMA_NODEMASK_CREATED = false;

	free(bmp);
}

long
get_mempolicy(int *policy, const unsigned long* nmask,
		unsigned long maxnode, void* addr, int flags)
{
	// http://man7.org/linux/man-pages/man2/get_mempolicy.2.html
	if (flags == 0) {
		// When flags is 0, addr must be specified as NULL.
		klee_assert(addr == NULL);

		// If flags is specified as 0, then information about the calling
		// thread's default policy (as set by set_mempolicy(2)) is returned, in
		// the buffers pointed to by mode and nodemask.  The value returned in
		// these arguments may be used to restore the thread's policy to its
		// state at the time of the call to get_mempolicy() using set_mempolicy(2).
		*policy = 0;

		// On success, get_mempolicy() returns 0; on error, -1 is returned and
		// errno is set to indicate the error.
		return 0;
	}

	klee_abort();
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

uid_t
getuid(void)
{
	// No errors: "These functions are always successful." -- http://man7.org/linux/man-pages/man2/getuid.2.html
	return 0; // We are root! well, we pretend to be, at least
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
	// http://man7.org/linux/man-pages/man2/mmap.2.html

	if(fd == DEV_ZERO_FD) {
		// Null address please, let's keep semantics easy to handle
		klee_assert(addr == NULL);

		// No offset plz
		klee_assert(offset == 0);

		// Easy flags
		klee_assert((flags & MAP_PRIVATE) == MAP_PRIVATE);

		// Read-only memory, we enforce even stronger semantics by disallowing reads with forbid_access
		klee_assert((prot & PROT_READ) == PROT_READ);

		// don't mmap twice
		klee_assert(DEV_ZERO_MMAPPED_SIZE == -1);

		DEV_ZERO_MMAPPED_SIZE = length;
		DEV_ZERO_MMAPPED_MEM = malloc(DEV_ZERO_MMAPPED_SIZE);
		memset(DEV_ZERO_MMAPPED_MEM, 0, DEV_ZERO_MMAPPED_SIZE);
		klee_forbid_access(DEV_ZERO_MMAPPED_MEM, DEV_ZERO_MMAPPED_SIZE, "read-only mmapped memory");
		return DEV_ZERO_MMAPPED_MEM;
	}

	if(fd == HUGEPAGE_FD || fd == HUGEPAGE_ZERO_FD) {
		// We don't care about the address; TODO should we? maybe at least check it modulo the page size?

		// the hugepage is 2048kB
		klee_assert(length == 2048 * 1024);

		// We don't support any offset, either
		klee_assert(offset == 0);

		// R/W is easy to handle
		klee_assert((prot & (PROT_READ|PROT_WRITE)) == (PROT_READ|PROT_WRITE));

		// Hard to do proper semantics for these, but we're single-threaded, so...
		klee_assert((flags & (MAP_SHARED|MAP_POPULATE)) == (MAP_SHARED|MAP_POPULATE));

		for (int n = 0; n < HUGEPAGES_MMAP_COUNT; n++) {
			if (HUGEPAGES_MMAPPED_SIZE[n] == -1) {
				HUGEPAGES_MMAPPED_SIZE[n] = length;
				HUGEPAGES_MMAPPED_MEM[n] = malloc(HUGEPAGES_MMAPPED_SIZE[n]);
				memset(HUGEPAGES_MMAPPED_MEM[n], 0, HUGEPAGES_MMAPPED_SIZE[n]);
				return HUGEPAGES_MMAPPED_MEM[n];
			}
		}

		klee_abort(); // no available pages
	}

	if(fd == HUGEPAGE_INFO_FD) {
		// Simple semantics: no addr, known length, no offset
		klee_assert(addr == NULL);
		klee_assert(length == HUGEPAGE_INFO_SIZE);
		klee_assert(offset == 0);

		// R/W is easy to handle
		klee_assert((prot & (PROT_READ|PROT_WRITE)) == (PROT_READ|PROT_WRITE));

		// Hard to do proper semantics for this, but we're single-threaded, so...
		klee_assert((flags & MAP_SHARED) == MAP_SHARED);

		// Single mmap at a time
		klee_assert(HUGEPAGE_INFO_MMAPPED_MEM == NULL);

		HUGEPAGE_INFO_MMAPPED_MEM = malloc(HUGEPAGE_INFO_SIZE);
		memset(HUGEPAGE_INFO_MMAPPED_MEM, 0, HUGEPAGE_INFO_SIZE);
		return HUGEPAGE_INFO_MMAPPED_MEM;
	}

	klee_abort();
}

int
munmap(void* addr, size_t length)
{
	if (addr == DEV_ZERO_MMAPPED_MEM && addr != NULL) {
		klee_assert(length == DEV_ZERO_MMAPPED_SIZE);

		klee_allow_access(DEV_ZERO_MMAPPED_MEM, DEV_ZERO_MMAPPED_SIZE);
		free(DEV_ZERO_MMAPPED_MEM);
		DEV_ZERO_MMAPPED_SIZE = -1;

		// Upon successful completion, munmap() shall return 0; otherwise, it shall return -1 and set errno to indicate the error.
		// -- https://linux.die.net/man/3/munmap
		return 0;
	}


	for (int n = 0; n < HUGEPAGES_MMAP_COUNT; n++) {
		if (addr == HUGEPAGES_MMAPPED_MEM[n]) {
			klee_assert(length == HUGEPAGES_MMAPPED_SIZE[n]);
			HUGEPAGES_MMAPPED_SIZE[n] = -1;
			free(HUGEPAGES_MMAPPED_MEM[n]);
			return 0;
		}
	}

	if (addr == HUGEPAGE_INFO_MMAPPED_MEM) {
		free(HUGEPAGE_INFO_MMAPPED_MEM);
		HUGEPAGE_INFO_MMAPPED_MEM = NULL;
		return 0;
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


// We need __ctype_b_loc, but klee-uclibc doesn't give it to us unless we also enable other settings
// (such as enabling stdio)
// From the musl libc, Copyright © 2005-2014 Rich Felker, et al.
// File src/ctype/__ctype_b_loc.c
#if __BYTE_ORDER == __BIG_ENDIAN
#define X(x) x
#else
#define X(x) (((x)/256 | (x)*256) % 65536)
#endif
static const unsigned short table[] = {
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),
X(0x200),X(0x320),X(0x220),X(0x220),X(0x220),X(0x220),X(0x200),X(0x200),
X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),
X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),X(0x200),
X(0x160),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),
X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),
X(0x8d8),X(0x8d8),X(0x8d8),X(0x8d8),X(0x8d8),X(0x8d8),X(0x8d8),X(0x8d8),
X(0x8d8),X(0x8d8),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),
X(0x4c0),X(0x8d5),X(0x8d5),X(0x8d5),X(0x8d5),X(0x8d5),X(0x8d5),X(0x8c5),
X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),
X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),X(0x8c5),
X(0x8c5),X(0x8c5),X(0x8c5),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),
X(0x4c0),X(0x8d6),X(0x8d6),X(0x8d6),X(0x8d6),X(0x8d6),X(0x8d6),X(0x8c6),
X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),
X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),X(0x8c6),
X(0x8c6),X(0x8c6),X(0x8c6),X(0x4c0),X(0x4c0),X(0x4c0),X(0x4c0),X(0x200),
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
};
#undef X
static const unsigned short* const ptable = table+128;
const unsigned short** __ctype_b_loc(void)
{
	return (void*) &ptable;
}


int
sigsetjmp(sigjmp_buf env, int savesigs)
{
	// We don't support longjmp, so nothing to do here

	// setjmp() and sigsetjmp() return 0 if returning directly, and nonzero when returning from longjmp(3) or siglongjmp(3) using the saved context.
	// -- https://linux.die.net/man/3/sigsetjmp
	return 0;
}

// sigaction is implemented in klee-uclibc as a forward to a syscall, but it's easier to stub it directly
int
stub_sigaction(int signum, const struct sigaction *act, struct sigaction *oldact)
{
	// Signals aren't supported, just return success

	// sigaction() returns 0 on success; on error, -1 is returned, and errno is set to indicate the error.
	// -- http://man7.org/linux/man-pages/man2/sigaction.2.html
	return 0;
}

void
stub_external_init(void)
{
	klee_alias_function("sigaction", "stub_sigaction");
}
