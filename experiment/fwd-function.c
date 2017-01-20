#include <klee/klee.h>

struct packet
{
  int dst_ip;
  int src_ip;
};

int a_packet_sent = 0;

void recv_packet(struct packet* p)
{
  klee_make_symbolic(p, sizeof(struct packet), "received-packet");
}

void send_packet(struct packet* p)
{
  a_packet_sent = 1;
}

void forward()
{
  struct packet p;
  recv_packet(&p);
  if (p.dst_ip != 0xffaab10c)
    send_packet(&p);
}

int main()
{
  forward();
  if (a_packet_sent)
    klee_dump_constraints();
  return 0;
}
