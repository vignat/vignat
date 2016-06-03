#include <klee.h>
#include "net.h"

int pkt;

int* recv()
{
  if (klee_int("received_pred")) {
    pkt = klee_int("received_val");
    return &pkt;
  }
  return 0;
}

void send(int*)
{
  //do nothing.
}
