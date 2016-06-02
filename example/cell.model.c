
struct cell {};
//@ predicate cellp(struct cell* c, option<int> x);

struct cell* alloc()
//@ requires true;
//@ ensures result == 0 ? true : cellp(result, none);
{
  return klee_int("alloc_ptr");//may also enforce initialization,
  //but it will be caught in validator anyway
}

int full(struct cell* c)
//@ requires cellp(c, ?x);
//@ ensures (x != none ? result == 1 : result == 0) &*& cellp(c, x);
{
  if (klee_int("full")) return 1;
  return 0;
}

int push(struct cell* c, int x)
//@ requires cellp(c, none);
//@ ensures result == 1 ? cellp(c, some(x)) : cellp(c, none);
{
  if (klee_int("push_success")) return 1;
  return 0;
}

int pop(struct cell* c)
//@ requires cellp(c, some(?v));
//@ ensures cellp(c, none) &*& result == v;
{
  return klee_int("pop_val");
}
