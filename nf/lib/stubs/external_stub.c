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

// Globals
// TODO this is kind of hacky - we should have some kind of "symbol that is never equal to anything" for the FDs
static bool NUMA_INITIALIZED = false;
static bool NUMA_NODEMASK_CREATED = false;

static const int POS_UNOPENED = -1;
static const int POS_EOF = -2;

enum stub_file_kind {
	KIND_FILE,
	KIND_DIRECTORY,
	KIND_LINK
};

struct stub_mmap {
	void* mem;
	size_t mem_len;
};

struct stub_file {
	// Folders MUST NOT have a trailing slash
	// Unix-like multi-slash simplification (e.g. /a//b == /a/b) is NOT supported
	char* path;

	// Either: (file or symlink)
	char* content;
	// Or: (folder)
	int* children;
	int children_len;

	// In the file and folder cases, this keeps track of progress
	int pos;

	// Set at creation time
	enum stub_file_kind kind;

	// Support flock
	bool locked;

	// Support mmap (2 max)
	struct stub_mmap mmaps[2];
	size_t mmaps_len;
};
static struct stub_file FILES[1024];

// Special case: the page map
static char* FILE_CONTENT_PAGEMAP = (char*) -100;

// Special case: the hugepage info file, which is truncated
static char* FILE_CONTENT_HPINFO = (char*) -200;

struct stub_device {
	char* name;
	void* mem;
	size_t mem_len;
};
static struct stub_device DEVICES[2];

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
	if (mode == F_OK) {
		for (int n = 0; n < sizeof(FILES)/sizeof(FILES[0]); n++) {
			if (FILES[n].path != NULL && !strcmp(pathname, FILES[n].path)) {
				return 0;
			}
		}

		// Other CPUs
		const char* cpu_prefix = "/sys/devices/system/cpu/cpu";
		if (!strncmp(pathname, cpu_prefix, strlen(cpu_prefix))) {
			return -1; // TODO
		}
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
	if (!strcmp(file, "/proc/cpuinfo") && oflag == O_RDONLY) {
		return -1; // TODO
	}

	// NUMA map, unsupported for now
	if (!strcmp(file, "/proc/self/numa_maps") && oflag == O_RDONLY) {
		return -1; // TODO
	}

	// Generic
	enum stub_file_kind desired_kind = ((oflag & O_DIRECTORY) == O_DIRECTORY) ? KIND_DIRECTORY : KIND_FILE;
	for (int n = 0; n < sizeof(FILES)/sizeof(FILES[0]); n++) {
		if (FILES[n].path != NULL && !strcmp(file, FILES[n].path) && FILES[n].kind == desired_kind) {
			klee_assert(FILES[n].pos == POS_UNOPENED);

			FILES[n].pos = 0;

			return n;
		}
	}

	// Other CPUs
	const char* cpu_prefix = "/sys/devices/system/cpu/cpu";
	if (!strncmp(file, cpu_prefix, strlen(cpu_prefix)) && oflag == O_RDONLY) {
		return -1; // TODO
	}

for(int n = 0;n<strlen(file);n++){klee_print_expr("x", file[n]);}
	// Not supported!
	klee_abort();
}

int
fcntl(int fd, int cmd, ...)
{
	klee_assert(cmd == F_SETFD);

        va_list args;
        va_start(args, cmd);

	int arg = va_arg(args, int);
	klee_assert(arg == FD_CLOEXEC);

	klee_assert(FILES[fd].children != NULL);

	return 0;
}

int
flock(int fd, int operation)
{
	klee_assert(FILES[fd].pos != POS_UNOPENED);

	// We assign similar semantics to EX and SH since we're single-threaded
	if ((operation & LOCK_EX) == LOCK_EX || (operation & LOCK_SH) == LOCK_SH) {
		// POSIX locks are re-entrant
		FILES[fd].locked = true;
		return 0;
	}

	if ((operation & LOCK_UN) == LOCK_UN) {
		klee_assert(FILES[fd].locked);
		FILES[fd].locked = false;
		return 0;
	}

	klee_abort();
}

int
fstat(int fd, struct stat* buf)
{
	klee_assert(FILES[fd].pos != POS_UNOPENED);
	klee_assert(FILES[fd].kind == KIND_DIRECTORY);

	memset(buf, 0, sizeof(struct stat));

	return 0;
}

int
ftruncate(int fd, off_t length)
{
	klee_assert(FILES[fd].pos != POS_UNOPENED);
	klee_assert(FILES[fd].kind == KIND_FILE);

	if (FILES[fd].content == FILE_CONTENT_HPINFO) {
		FILES[fd].content = (char*) malloc(length);
		memset(FILES[fd].content, 0, length);

		// On success, zero is returned. On error, -1 is returned, and errno is set appropriately.
		// -- https://linux.die.net/man/2/ftruncate
		return 0;
	}

	klee_abort();
}

off_t
lseek(int fd, off_t offset, int whence)
{
	klee_assert(FILES[fd].pos != POS_UNOPENED);
	klee_assert(FILES[fd].kind == KIND_FILE);

	if (FILES[fd].content == FILE_CONTENT_PAGEMAP) {
		klee_assert(whence == SEEK_SET);
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
	klee_assert(FILES[fd].pos != POS_UNOPENED);
	klee_assert(FILES[fd].kind == KIND_FILE);

	if (FILES[fd].content == FILE_CONTENT_PAGEMAP) {
		klee_assert(count == 8);
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

	klee_assert(count == 1);

	if (FILES[fd].pos < strlen(FILES[fd].content)) {
		*((char*) buf) = FILES[fd].content[FILES[fd].pos];
		FILES[fd].pos++;
		return 1;
	}

	FILES[fd].pos = POS_EOF;

	return 0;
}

int
close(int fd)
{
	klee_assert(FILES[fd].pos != POS_UNOPENED);

	FILES[fd].pos = POS_UNOPENED;
	FILES[fd].locked = false;

	// We do not remove mmapings:
	// "The mmap() function adds an extra reference to the file associated with the file descriptor fildes
	//  which is not removed by a subsequent close() on that file descriptor. This reference is removed when there are no more mappings to the file."
	// -- http://pubs.opengroup.org/onlinepubs/7908799/xsh/mmap.html

	return 0;
}

ssize_t
readlink(const char* pathname, char* buf, size_t bufsiz)
{
	for (int n = 0; n < sizeof(FILES)/sizeof(FILES[0]); n++) {
		if (FILES[n].path != NULL && !strcmp(pathname, FILES[n].path)) {
			klee_assert(FILES[n].kind == KIND_LINK);
			klee_assert(bufsiz > strlen(FILES[n].content));

			strcpy(buf, FILES[n].content);
			return strlen(FILES[n].content);
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

	klee_assert(FILES[fd].kind == KIND_DIRECTORY);
	klee_assert(FILES[fd].pos >= 0);
	klee_assert(FILES[fd].pos <= FILES[fd].children_len);

	if (FILES[fd].pos == FILES[fd].children_len) {
		FILES[fd].pos = POS_EOF;
		return 0;
	}

	int child_fd = FILES[fd].children[FILES[fd].pos];
klee_print_expr("child_fd", child_fd);
for(int n = 0;n<strlen(FILES[child_fd].path);n++){klee_print_expr("x", FILES[child_fd].path[n]);}
	char* filename = strrchr(FILES[child_fd].path, '/') + 1;
	strcpy(de->d_name, filename);
	de->d_reclen = len; // should bestrlen(de->d_name)
	de->d_type = FILES[child_fd].content == NULL ? DT_DIR : 0;

	FILES[fd].pos++;

	return len;
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

	klee_assert(FILES[fd].kind == KIND_FILE);

	// First off, are we trying to mmap device memory?
	for (int n = 0; n < sizeof(DEVICES)/sizeof(DEVICES[0]); n++) {
		if ((void*) FILES[fd].content == DEVICES[n].mem) {
			klee_assert(length == DEVICES[n].mem_len);

			return DEVICES[n].mem;
		}
	}

	// We don't really care about flags, since we're single-threaded

	// addr must be NULL, unless we're mmapping hugepages
	// TODO check the address somehow when it's a hugepage
	const char* hugepages_prefix = "/dev/hugepages";
	if (strncmp(FILES[fd].path, hugepages_prefix, strlen(hugepages_prefix))) {
		klee_assert(addr == NULL);
		klee_assert(length >= strlen(FILES[fd].content));
	} else {
		// if it's a hugepage, length is well-defined
		klee_assert(length % (2048 * 1024) == 0);
	}

	// Offsets not supported
	klee_assert(offset == 0);

	// don't mmap too many times
	klee_assert(FILES[fd].mmaps_len < sizeof(FILES[0].mmaps)/sizeof(FILES[0].mmaps[0]));

	void* mem = malloc(length);
	if ((prot & PROT_WRITE) != PROT_WRITE) {
		// Read-only memory, we enforce even stronger semantics by disallowing reads with forbid_access
		klee_forbid_access(mem, length, "mmapped read-only memory");
	}

	int m = FILES[fd].mmaps_len;
	FILES[fd].mmaps[m].mem = mem;
	FILES[fd].mmaps[m].mem_len = length;
	FILES[fd].mmaps_len++;

	return mem;
}

int
munmap(void* addr, size_t length)
{
	// Upon successful completion, munmap() shall return 0; otherwise, it shall return -1 and set errno to indicate the error.
	// -- https://linux.die.net/man/3/munmap

	for (int n = 0; n < sizeof(FILES)/sizeof(FILES[0]); n++) {
		for (int m = 0; m < FILES[n].mmaps_len; m++) {
			if (FILES[n].mmaps[m].mem == addr) {
				klee_assert(FILES[n].mmaps[m].mem_len == length);

				free(FILES[n].mmaps[m].mem);
				memset(&(FILES[n].mmaps[m]), 0, sizeof(struct stub_mmap));

				FILES[n].mmaps_len--;

				return 0;
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
	// Helper methods declarations
	char* stub_pci_name(int index);
	char* stub_pci_file(const char* device_name, const char* file_name);
	char* stub_pci_folder(const char* device_name);
	char* stub_pci_addr(size_t addr);
	int stub_add_file(char* path, char* content);
	int stub_add_link(char* path, char* content);
	int stub_add_folder_array(char* path, int children_len, int* children);
	int stub_add_folder(char* path, int children_len, ...);


	// Alias definitions
	klee_alias_function("sigaction", "stub_sigaction");


	// Files initialization
	int f = 0;
	memset(FILES, 0, sizeof(FILES));

	// PCI-related files
	int devices_count = sizeof(DEVICES)/sizeof(DEVICES[0]);
	int* dev_folders = (int*) malloc(devices_count * sizeof(int));
	for (int n = 0; n < devices_count; n++) {
		char* dev = stub_pci_name(n);
		size_t mem_len = 1 << 20; // 2^20 bytes
		void* mem = malloc(mem_len);
		memset(mem, 0, mem_len);

		struct stub_device stub_dev = {
			.name = dev,
			.mem = mem,
			.mem_len = mem_len
		};
		DEVICES[n] = stub_dev;

		// Basic files
		int vendor_fd = stub_add_file(stub_pci_file(dev, "vendor"), "32902\n"); // ixgbe
		int device_fd = stub_add_file(stub_pci_file(dev, "device"), "5546\n"); // ixgbe
		int subvendor_fd = stub_add_file(stub_pci_file(dev, "subsystem_vendor"), "0\n"); // any
		int subdevice_fd = stub_add_file(stub_pci_file(dev, "subsystem_device"), "0\n"); // any
		int class_fd = stub_add_file(stub_pci_file(dev, "class"), "16777215\n"); // ixgbe
		int maxvfs_fd = stub_add_file(stub_pci_file(dev, "max_vfs"), "0\n"); // no virtual functions
		int numanode_fd = stub_add_file(stub_pci_file(dev, "numa_node"), "0\n"); // NUMA node 0

		// Driver symlink
		int driver_fd = stub_add_link(stub_pci_file(dev, "driver"), "/drivers/igb_uio");

		// 'uio' folder, itself containing an empty folder 'uio0'
		// One single entry, called uio0
		int uio0_fd = stub_add_folder(stub_pci_file(dev, "uio/uio0"), 0);
		int uio_fd = stub_add_folder(stub_pci_file(dev, "uio"), 1, uio0_fd);

		// Resources file
		// Multiple lines; each line has the format <start addr> <end addr> <flags>
		// all of which are 64-bit numbers in hexadecimal notation (starting with 0x)
		// Flag 0x200 is "memory", i.e. the addresses designate a DMA location
		// DPDK interprets 6 lines max (PCI_MAX_RESOURCE)

		// One single resource, rest are empty
		char* resource_format =
			"%s %s 0x0000000000000200\n"
			"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
			"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
			"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
			"0x0000000000000000 0x0000000000000000 0x0000000000000000\n"
			"0x0000000000000000 0x0000000000000000 0x0000000000000000\n";
		char resource_content[1024];
		snprintf(resource_content, sizeof(resource_content), resource_format,
				stub_pci_addr((size_t) DEVICES[n].mem), stub_pci_addr((size_t) DEVICES[n].mem + DEVICES[n].mem_len - 1));

		int resource_fd = stub_add_file(stub_pci_file(dev, "resource"), strdup(resource_content));

		// Since we say we have one resource, we need to create it...
		int resource0_fd = stub_add_file(stub_pci_file(dev, "resource0"), (char*) DEVICES[n].mem);

		dev_folders[n] = stub_add_folder(stub_pci_folder(dev), 11,
					vendor_fd, device_fd, subvendor_fd, subdevice_fd,
					class_fd, maxvfs_fd, numanode_fd, driver_fd,
					uio_fd, resource_fd, resource0_fd);
	}

	stub_add_folder_array("/sys/bus/pci/devices", devices_count, dev_folders);


	// Hugepages properties
	int huge_res_fd = stub_add_file("/sys/kernel/mm/hugepages/hugepages-2048kB/resv_hugepages", "0\n"); // number of reserved hugepages
	int huge_free_fd = stub_add_file("/sys/kernel/mm/hugepages/hugepages-2048kB/free_hugepages", "1\n"); // number of free hugepages
	int huge_2048_fd = stub_add_folder("/sys/kernel/mm/hugepages/hugepages-2048kB", 2, huge_res_fd, huge_free_fd);
	stub_add_folder("/sys/kernel/mm/hugepages", 1, huge_2048_fd);

	// /sys stuff
	// TODO: We pretend CPU 0 / NUMA node 0 exist, but what about others?
	stub_add_file("/sys/devices/system/cpu/cpu0/topology/core_id", "0"); // CPU 0 is core ID 0
	stub_add_folder("/sys/devices/system/node/node0/cpu0", 0);

	// /proc stuff
	stub_add_file("/proc/mounts", "hugetlbfs /dev/hugepages hugetlbfs rw,relatime 0 0\n"); // only hugepages, what DPDK cares about
	stub_add_file("/proc/meminfo", "Hugepagesize:       2048 kB\n"); // only hugepages, what DPDK cares about
	stub_add_file("/proc/self/pagemap", FILE_CONTENT_PAGEMAP);

	// Hugepages folder (empty)
	int dot_fd = stub_add_file("./.", ""); // need a / in the name, see remark in stub_file
	stub_add_folder("/dev/hugepages", 1, dot_fd); // DPDK relies on there being at least 1 file in there

	// HACK this folder is opened as a file for locking and as a folder for enumerating...
	stub_add_file("/dev/hugepages", "");

	// HACK those two files exist but are not bound to their folder (defined above)...
	stub_add_file("/dev/hugepages/rte", "");
	stub_add_file("/dev/hugepages/rtemap_0", "");

	// /var stuff
	stub_add_file("/var/run/.rte_hugepage_info", FILE_CONTENT_HPINFO);

	// UIO stuff
	stub_add_file("/sys/class/uio/uio0/device/config", "");
	stub_add_file("/dev/uio0", ""); // HACK as long as it's not used, we can pretend it's a file (it's a device...)

	// Other devices
	stub_add_file("/dev/zero", ""); // HACK as long as it's not read, we can pretend it doesn't contain anything
}


// Helper methods - not part of the external stubs
char*
stub_pci_name(int index)
{
	klee_assert(index >= 0 && index < 10); // simpler

	char buffer[1024];
	snprintf(buffer, sizeof(buffer), "0000:00:00.%d", index);
	return strdup(buffer);
}

char*
stub_pci_file(const char* device_name, const char* file_name) {
	char buffer[1024];
	snprintf(buffer, sizeof(buffer), "/sys/bus/pci/devices/%s/%s", device_name, file_name);
	return strdup(buffer);
}

char*
stub_pci_folder(const char* device_name) {
	char buffer[1024];
	snprintf(buffer, sizeof(buffer), "/sys/bus/pci/devices/%s", device_name);
	return strdup(buffer);
}

char*
stub_pci_addr(size_t addr)
{
	char* buffer = "0x0000000000000000";
	int pos = strlen(buffer) - 1;
	while (addr > 0) {
		size_t digit = addr % 16;
		addr /= 16;

		if (digit < 10) {
			buffer[pos] = '0' + digit;
		} else {
			buffer[pos] = 'A' + (digit - 10);
		}

		pos--;
	}

	return strdup(buffer);
}

static int file_counter;
int
stub_add_file(char* path, char* content)
{
	struct stub_file file = {
		.path = path,
		.content = content,
		.children = NULL,
		.children_len = 0,
		.pos = POS_UNOPENED,
		.kind = KIND_FILE,
		.locked = false,
		.mmaps = NULL,
		.mmaps_len = 0
	};


	int fd = file_counter;
	file_counter++;

	FILES[fd] = file;

	return fd;
}

int
stub_add_link(char* path, char* content)
{
	int fd = stub_add_file(path, content);
	FILES[fd].kind = KIND_LINK;
	return fd;
}

int
stub_add_folder_array(char* path, int children_len, int* children)
{
        struct stub_file file = {
		.path = path,
		.content = NULL,
		.children = children,
		.children_len = children_len,
		.pos = POS_UNOPENED,
		.kind = KIND_DIRECTORY,
		.locked = false,
		.mmaps = NULL,
		.mmaps_len = 0
	};

        int fd = file_counter;
        file_counter++;

	FILES[fd] = file;

        return fd;
}

int
stub_add_folder(char* path, int children_len, ...)
{
	va_list args;
	va_start(args, children_len);

	int* children = (int*) malloc(children_len * sizeof(int));
	for (int n = 0; n < children_len; n++) {
		children[n] = va_arg(args, int);
	}

	return stub_add_folder_array(path, children_len, children);
}
