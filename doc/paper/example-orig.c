#include <klee/klee.h>

#define CAP 512

int main() {
  int data[CAP] = {};

  while(1) {
    int i = klee_range(0,CAP,"i");
    int x = data[i];
    ++x;
    if (x == 4) x = 2;
    data[i] = x;
    assert(x < 4);
  }
  return 0;
}
