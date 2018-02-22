#include <stddef.h>

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
