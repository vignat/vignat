#include "cell.h"

int main() {
  while(1) {
    int p;
    if (recv(&p)) {
      if (full()) {
        send(&p);
        int* sp;
        pop(&sp); // no check.
        send(*sp);
      } else {
        push(&p);
      }
    }
  }// dead reference to p
}
