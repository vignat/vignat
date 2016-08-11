
#include <klee/klee.h>

#define CAP 512

struct Array {
  int data[CAP];
};

int array_read(struct Array* arr, int i) {
  int ret = klee_range(0, 4, "ret");
  return ret;
}

void array_write(struct Array* arr, int i, int val) {
  klee_assert(0 <= val && val < 4);
}

int main() {
  struct Array data;
  {
    int i = klee_range(0, CAP, "i");
    int x = array_read(&data, i);
    ++x;
    if (x == 4) x = 2;
    array_write(&data, i, x);
    assert(x < 4);
  }
  return 0;
}
