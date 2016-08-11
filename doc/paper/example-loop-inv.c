#include <klee/klee.h>

#define CAP 512

int main() {
  int data[CAP] = {};
  for (int i = 0; i < CAP; ++i) klee_assert(data[i] < 4);
  klee_make_symbolic(data, sizeof(data), "data");
  for (int i = 0; i < CAP; ++i) klee_assume(data[i] < 4);
  {
    int i = klee_range(0, CAP, "i");
    int x = data[i];
    ++x;
    if (x == 4) x = 2;
    data[i] = x;
    assert(x < 4);
  }
  for (int i = 0; i < CAP; ++i) klee_assert(data[i] < 4);
  return 0;
}
