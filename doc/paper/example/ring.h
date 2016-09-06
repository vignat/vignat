#include "packet.h"

bool ring_full();
bool ring_empty();
void ring_push(struct packet* p);
void ring_pop(struct packet* p);
