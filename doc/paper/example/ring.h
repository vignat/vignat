#include "packet.h"

bool ring_full();
bool ring_empty();
void ring_push_back(struct packet* p);
void ring_pop_front(struct packet* p);
