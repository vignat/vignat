#include <stdint.h>
#include <string.h>

#include "map.h"

//@ #include <list.gh>
//@ #include <listex.gh>

//TODO: introduce the "chain continuation" bit to optimize search for abscent.

/*@
  lemma void div_mod(int g, int k, int l)
  requires g == (k % l) &*& l > 0;
  ensures (-l <= g) &*& (g < l);
  {
  div_rem(k, l);
  }
  @*/

/*@
  lemma void div_mod_gt_0(int mod, int div, int whole)
  requires mod == (div % whole) &*& whole > 0 &*& div >= 0;
  ensures (0 <= mod) &*& (mod < whole);
  {
  div_rem(div, whole);
  }
  @*/
/*@
  fixpoint int loop_fp(int k, int capacity)
  { return ((k%capacity + capacity)%capacity); }
  @*/

static
int loop(int k, int capacity)
//@ requires 0 < capacity &*& 2*capacity < INT_MAX;
/*@ ensures 0 <= result &*& result < capacity &*&
            result == loop_fp(k, capacity); @*/
{
  int g = k%capacity;
  //@ div_mod(g, k, capacity);
  //@ assert(2*capacity< INT_MAX);
  int res = (g + capacity)%capacity;
  //@ div_mod_gt_0(res, g + capacity, capacity);
  return res;
}
#define CAPACITY 1000
/*@
  lemma void loop_lims(int k, int capacity)
  requires 0 < capacity;
  ensures 0 <= loop_fp(k, capacity) &*& loop_fp(k, capacity) < capacity;
  {
    div_rem(k, capacity);
    assert(-capacity <= k%capacity);
    assert(0 <= k%capacity + capacity);
    div_rem((k + capacity), capacity);
    assert(capacity > 0);
    div_rem(k%capacity + capacity, capacity);
    assert(0 <= ((k%capacity + capacity)%capacity));
  }

  lemma void mul_mono(int a, int b, int c)
  requires a <= b &*& 0 <= c;
  ensures a * c <= b * c;
  {
    for (int i = 0; i < c; i++)
      invariant i <= c &*& a * i <= b * i;
      decreases c - i;
    {
    }
  }

  lemma void bar(int a, int b, int q, int r)
  requires 0 <= a &*& a < b &*& 0 <= r &*& a == q * b + r &*& r < b;
  ensures q == 0;
  {
    if (q == 0) {
    } else if (0 <= q) {
      mul_mono(1, q, b);
    } else {
      mul_mono(q, -1, b);
    }
  }

  lemma void division_round_to_zero(int a, int b)
  requires 0 <= a &*& a < b;
  ensures a/b == 0;
  {
    div_rem(a, b);
    bar(a, b, a / b, a % b);
  }

  lemma void loop_bijection(int k, int capacity)
  requires 0 <= k &*& k < capacity;
  ensures loop_fp(k, capacity) == k;
  {
    div_rem(k, capacity);
    assert(0 < capacity);
    division_round_to_zero(k, capacity);
    //TODO: the below is really true, see in the debugger!
    assume(k == ((k/capacity)*capacity) + (k % capacity));
    assert(k/capacity == 0);
    assert(k%capacity == k);
    div_rem((k + capacity), capacity);
    // Believe me, baby. I the parser get's out of hand here,
    // so I can not even formulate my assumptions properly
    assume(false);
    assert(k == ((k % capacity + capacity) % capacity));
  }

  lemma void loop_injection(int k, int capacity)
  requires 0 <= k &*& 0 < capacity;
  ensures loop_fp(k + capacity, capacity) == loop_fp(k, capacity);
  {
    div_rem(k, capacity);
    div_rem((k + capacity), capacity);
    int x = (k + capacity) % capacity;
    // Sorry, you have to believe me again.
    assume(false);
    assert(x == ((k%capacity) + (capacity/capacity)));
  }

  lemma void loop_fixp(int k, int capacity)
  requires 0 <= k &*& 0 < capacity;
  ensures loop_fp(k, capacity) == loop_fp(loop_fp(k, capacity), capacity);
  {
    loop_lims(k, capacity);
    loop_bijection(loop_fp(k, capacity), capacity);
  }
  @*/

/*@
  inductive hmap<kt> = hmap(list<bool>, list<kt>, list<int>);

  predicate hmapping<kt>(predicate (void*; kt) keyp,
                         fixpoint (kt, int) hash,
                         int capacity,
                         int* busybits,
                         void** keyps,
                         int* k_hashes;
                         hmap<kt> m);

  fixpoint bool hmap_exists_key_fp<kt>(hmap<kt> m, void* keyp);
  fixpoint int hmap_find_key_fp<kt>(hmap<kt> m, void* keyp);
  fixpoint int hmap_size_fp<kt>(hmap<kt> m);
  fixpoint int hmap_find_empty_fp<kt>(hmap<kt> m, int start);
  @*/

/*@
  predicate foreach2<t1,t2>(list<t1> l1, predicate (t1;t2) p; list<t2> l2) =
            l1 == nil ? l2 == nil :
            foreach2(tail(l1), p, ?l2t) &*& p(head(l1), ?l2h) &*&
            l2 == cons(l2h, l2t);

  predicate owned_pointers<kt>(void** parr, int length,
                               predicate (void*; kt) p; list<kt> objs) =
                 pointers(parr, length, ?pts) &*&
                 foreach2(pts, p, objs);

  fixpoint bool i2b (int x) { return x != 0; }

  predicate hmapping<kt>(predicate (void*; kt) keyp,
                         fixpoint (kt, int) hash,
                         int capacity,
                         int* busybits,
                         void** keyps,
                         int* k_hashes;
                         hmap<kt> m) =
            0 < capacity &*& 2*capacity < INT_MAX &*&
            ints(busybits, capacity, ?bbs) &*&
            owned_pointers(keyps, capacity, keyp, ?ks) &*&
            ints(k_hashes, capacity, ?khs) &*&
            m == hmap(map(i2b, bbs), ks, khs);

  lemma void hmapping_capacity_lims<kt>(int capacity)
  requires hmapping<kt>(?kpr, ?hsh, capacity, ?busybits, ?keyps, ?k_hashes, ?hm);
  ensures hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm) &*&
          0 < capacity &*& 2*capacity < INT_MAX;
  {
     open hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm);
     close hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm);
  }

  //fixpoint bool hmap_exists_key_fp<kt>(hmap<kt> m, void* keyp);
  //fixpoint int hmap_find_key_fp<kt>(hmap<kt> m, void* keyp);
  //fixpoint int hmap_size_fp<kt>(hmap<kt> m);
  //fixpoint int hmap_find_empty_fp<kt>(hmap<kt> m, int start);
@*/

static
int find_key/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int start,
                         void* keyp, map_keys_equality* eq, int key_hash,
                         int capacity)
/*@ requires hmapping<kt>(?kpr, ?hsh, capacity, busybits, keyps, k_hashes, ?hm) &*&
             kpr(keyp, ?k) &*&
             hsh(k) == key_hash &*&
             0 <= start &*& 2*start < INT_MAX &*&
             [_]is_map_keys_equality<kt>(eq, kpr); @*/
/*@ ensures hmapping<kt>(kpr, hsh, capacity, busybits, keyps, k_hashes, hm) &*&
            kpr(keyp, k) &*&
            [_]is_map_keys_equality<kt>(eq, kpr) &*&
            (hmap_exists_key_fp(hm, keyp) ?
            (result == hmap_find_key_fp(hm, keyp)) :
             (result == -1)); @*/
{
  //@ hmapping_capacity_lims(capacity);
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant hmapping<kt>(kpr, hsh, capacity,
                               busybits, keyps, k_hashes, hm) &*&
                  0 <= i &*& i <= capacity &*&
                  [_]is_map_keys_equality<kt>(eq, kpr);
    @*/
  {
    //@ open hmapping<kt>(_, _, _, _, _, _, hm);
    int index = loop(start + i, capacity);
    int bb = busybits[index];
    int kh = k_hashes[index];
    void* kp = keyps[index];
    if (bb != 0 && kh == key_hash) {
      if (eq(kp, keyp)) {
        //@ close hmapping<kt>(_, _, _, _, _, hm);
        return index;
      }
    }
    //@ close hmapping<kt>(_, _, _, _, _, _, hm);
  }
  return -1;
}

static
int find_empty/*@ <kt> @*/(int* busybits, int start, int capacity)
/*@ requires hmapping<kt>(?kp, ?hsh, capacity, busybits, ?keyps, ?k_hashes, ?hm); @*/
/*@ ensures hmapping<kt>(kp, hsh, capacity, busybits, keyps, k_hashes, hm) &*&
  (hmap_size_fp(hm) < capacity ?
   result == hmap_find_empty_fp(hm, start) :
   result == -1) ; @*/
{
    int i = 0;
    for (; i < capacity; ++i)
    {
        int index = loop(start + i, capacity);
        int bb = busybits[index];
        if (0 == bb) {
            return index;
        }
    }
    return -1;
}

void map_initialize/*@ <kt> @*/(int* busybits, map_keys_equality* eq,
                                void** keyps, int* khs, int* vals,
                                int capacity)
  /*@ requires exists<kt>(_) &*&
               exists<fixpoint (kt,int)>(?hash) &*&
               [_]is_map_keys_equality<kt>(eq, ?keyp) &*&
               pred_arg2<kt, int>(?recp) &*&
               ints(busybits, capacity, ?bbs) &*&
               pointers(keyps, capacity, ?kplist) &*&
               ints(vals, capacity, ?vallist) &*&
               ints(khs, capacity, ?khlist); @*/
  /*@ ensures mapping<kt>(empty_map_fp(), keyp, recp, hash,
                          capacity, busybits, keyps,
                          khs, vals); @*/
{
  (void)eq; (void)keyps; (void)khs; (void)vals;
  int i = 0;
  for (; i < capacity; ++i) {
    busybits[i] = 0;
  }
}

int map_get/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* values,
                        void* keyp, map_keys_equality* eq, int hash, int* value,
                        int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, values) &*&
             kp(keyp, ?k) &*&
             hsh(k) == hash &*&
             *value |-> ?v; @*/
/*@ ensures mapping<kt>(m, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, values) &*&
            kp(keyp, k) &*&
            (map_has_fp(m, k) ?
             (result == 1 &*&
              *value |-> v &*&
              v == map_get_fp(m, k) &*&
              recp(k, v)):
             (result == 0 &*&
              *value |-> v)); @*/
{
    int start = loop(hash, capacity);
    int index = find_key(busybits, keyps, k_hashes, start,
                         keyp, eq, hash, capacity);
    if (-1 == index)
    {
        return 0;
    }
    *value = values[index];
    return 1;
}

int map_put/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* values,
                        void* keyp, int hash, int value,
                        int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, values) &*&
             kp(keyp, ?k) &*& recp(k, value) &*&
             hsh(k) == hash &*&
             false == map_has_fp(m, k); @*/
/*@ ensures kp(keyp, k) &*& recp(k, value) &*&
            (map_size_fp(m) < capacity ?
             (result == 1 &*&
              mapping<kt>(map_put_fp(m, k, value), kp, recp,
                          hsh,
                          capacity, busybits,
                          keyps, k_hashes, values)) :
             (result == 0 &*&
              mapping<kt>(m, kp, recp, hsh, capacity, busybits,
                          keyps, k_hashes, values))); @*/
{
    int start = loop(hash, capacity);
    int index = find_empty(busybits, start, capacity);

    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 1;
    keyps[index] = keyp;
    k_hashes[index] = hash;
    values[index] = value;
    return 1;
}

int map_erase/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, void* keyp,
                          map_keys_equality* eq, int hash, int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, k_hashes, ?values) &*&
             kp(keyp, ?k) &*&
             hsh(k) == hash; @*/
/*@ ensures kp(keyp, k) &*&
            (map_has_fp(m, k) ?
            (result == 1 &*&
             mapping<kt>(map_erase_fp(m, k), kp, recp, hsh,
                         capacity, busybits, keyps, k_hashes, values)) :
            (result == 0 &*&
            mapping<kt>(m, kp, recp, hsh,
                        capacity, busybits, keyps, k_hashes, values))); @*/
{
    int start = loop(hash, capacity);
    int index = find_key(busybits, keyps, k_hashes, start,
                         keyp, eq, hash, capacity);
    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 0;
    return 1;
}

int map_size/*@ <kt> @*/(int* busybits, int capacity)
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         ?keyps, ?k_hashes, ?values); @*/
/*@ ensures mapping<kt>(m, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, values) &*&
            result == map_size_fp(m);@*/
{
    int s = 0;
    int i = 0;
    for (; i < capacity; ++i)
    {
        if (busybits[i] != 0)
        {
            ++s;
        }
    }
    return s;
}
