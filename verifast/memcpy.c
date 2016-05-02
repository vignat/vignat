#include <string.h>
#include <stdlib.h>

//@ #include <listex.gh>

int foo()
//@ requires exists<bool>(?lala) &*& (lala? exists<int>(?xa) : exists<real>(?xi)) &*& exists<fixpoint (int, int)>(?f);
//@ ensures result == 0;
{
  return 0;
}

struct A {
  int x;
  int y;
};

/*@
  predicate real_A(pair<int, int> v;) = INT_MIN <= fst(v) &*& fst(v) <= INT_MAX &*& INT_MIN <= snd(v) &*& snd(v) <= INT_MAX;
  predicate A(struct A* ptr; pair<int, int> v) = ptr->x |-> ?x &*& ptr->y |-> ?y &*& real_A(pair(x,y)) &*& v == pair(x,y);
  @*/

/*@
fixpoint list<char> chars_of_A(pair<int, int> a) {
  switch(a){case pair<int, int>(x, y): return append(chars_of_int(x), chars_of_int(y)); }
}

fixpoint pair<int, int> A_of_chars(list<char> chs) {
  return pair<int, int>(int_of_chars(take(4, chs)), int_of_chars(drop(4, chs)));
}


lemma void chars_within_limits_distr(int n, list<char> chs);
requires true == chars_within_limits(chs);
ensures true == chars_within_limits(chs) &*& true == chars_within_limits(take(n, chs)) &*& true == chars_within_limits(drop(n, chs));

lemma void chars_within_limits_append(list<char> chs1, list<char> chs2);
requires true == chars_within_limits(chs1) &*& true == chars_within_limits(chs2);
ensures true == chars_within_limits(chs1) &*& true == chars_within_limits(chs2) &*& true == chars_within_limits(append(chs1, chs2));

lemma void chars_of_int_within_limits(int a);
requires INT_MIN <= a &*& a <= INT_MAX;
ensures true == chars_within_limits(chars_of_int(a));

lemma void A_to_bytes(struct A* a)
requires A(a, ?val);
ensures chars((void*)a, sizeof(struct A), chars_of_A(val)) &*& chars_within_limits(chars_of_A(val)) == true;
{
  open A_x(a,?x);
  open A_y(a,?y);
  
  assume((void*)&a->y == (void*)&a->x + sizeof(int));
  assume(sizeof(struct A) == (sizeof(int) + sizeof(int)));
  integer_to_chars((void*)&a->x);
  integer_to_chars((void*)&a->y);
  chars_join((void*)a);
  chars_of_int_within_limits(x);
  chars_of_int_within_limits(y);
  chars_within_limits_append(chars_of_int(x), chars_of_int(y));
}

lemma void bytes_to_A(void* a)
requires chars((void*)a, sizeof(struct A), ?chs) &*& true == chars_within_limits(chs);
ensures A(a, A_of_chars(chs));
{
  assume(sizeof(struct A) == (sizeof(int) + sizeof(int)));
  struct A* aa = a;
  assume((void*)&aa->y == (void*)&aa->x + sizeof(int));
  chars_split((void*)a, sizeof(int));
  chars_to_integer((void*)&aa->x);
  chars_to_integer((void*)&aa->y);
  chars_within_limits_distr(sizeof(int), chs);
  int_of_chars_size(take(4, chs));
  close A_x(a,_);
  close A_y(a,_);
}

lemma void A_of_chars_of_A(pair<int,int> a)
requires real_A(a);
ensures A_of_chars(chars_of_A(a)) == a &*& real_A(a);
{
  switch(a){case pair(x, y):
  
  assume(sizeof(struct A) == (sizeof(int) + sizeof(int)));
  open real_A(a);
  assert(sizeof(int) == length(chars_of_int(x)));
  take_append(sizeof(int), chars_of_int(x), chars_of_int(y));
  drop_append(sizeof(int), chars_of_int(x), chars_of_int(y));
  close real_A(a);
     return; }
}

lemma void A_to_bytes_to_A(pair<int,int> a)
requires A(?ptr, a);
ensures A(ptr, a) &*& A_of_chars(chars_of_A(a)) == a;
{
  open A(ptr, a);
  A_of_chars_of_A(a);
  close A(ptr, a);
}
@*/

void* clone(void* a)
//@ requires A(a, ?val);
/*@ ensures A(a, val) &*&
            (result == 0 ? true : (malloc_block_A(result) &*& A(result, val))); @*/
{
  struct A* ret = malloc(sizeof(struct A));
  if (ret == 0) return 0;
  //@ A_to_bytes_to_A(val);
  //@ A_to_bytes(a);
  //@ A_to_bytes(ret);
  memcpy(ret, a, sizeof(struct A));
  //@ bytes_to_A(a);
  //@ bytes_to_A(ret);
  return ret;
}

#if 0
/*@

lemma void X_to_bytes<t>(predicate (void*, t) Xp, fixpoint (t, list<char>) chars_of_X)(void* x);
requires Xp(x, ?val);
ensures chars((void*)x, sizeof(struct A), chars_of_X(val)) &*& chars_within_limits(chars_of_X(val)) == true;

@*/

void* clone_gen/*@ <t> @*/(void* x, int size)
/*@ requires exists<predicate (void*;t)>(?p) &*&
             exists<fixpoint (t, list<char>)>(chars_of_X) &*&
             exists<fixpoint (list<char>, t)>(X_of_chars) &*& p(x, ?v) &*& size > 0; @*/
/*@ ensures p(x, v) &*&
            (result == 0 ? true : (p(result, v))); @*/
{
   void *ret = malloc(size);
   if (ret == 0) return 0;
   return x;
}
#endif
//@ fixpoint int haha(int x);

int main ()
//@ requires true;
//@ ensures true;
{
  struct A a;
  struct A* b = clone(&a);
  if (b) free(b);
  //@close exists<fixpoint (int, int)>(haha);
  //@close exists<bool>(true);
  //@close exists<real>(3.41);
  //@close exists<int>(13);
  return foo();
}
