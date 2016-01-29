#ifndef _BOUNDPTR_H_INCLUDED_
#define _BOUNDPTR_H_INCLUDED_

#include <stdint.h>
#include <stddef.h>

typedef struct boundptr {
  uint8_t *ptr;
  size_t size;
} boundptr;

static inline boundptr wrap_ptr(uint8_t* ptr, size_t size) {
  struct boundptr ret = {.ptr = ptr, .size = size};
  return ret;
}

#endif //_BOUNDPTR_H_INCLUDED_
