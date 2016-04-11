#include <stdint.h>
#include <string.h>

#include "map.h"

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
//@ requires true;
/*@ ensures 0 <= result &*& result < capacity &*&
            result == loop_fp(k, capacity); @*/
{
  int g = k%capacity;
  //@ div_mod(g, k, CAPACITY);
  int res = (g + capacity)%capacity;
  //@ div_mod_gt_0(res, g + CAPACITY, CAPACITY);
  return res;
}

/*@
  inductive hmap<kt> = hmap(list<pair<bool, pair<kt, int> > >);

  predicate hmapping<kt>(hmap<kt> m,
                         predicate (void*, kt) keyp,
                         fixpoint (kt, int) hash,
                         int capacity,
                         int* busybits,
                         void** keyps,
                         int* k_hashes);

  fixpoint bool hmap_exists_key_fp<kt>(hmap<kt> m, void* keyp);
  fixpoint int hmap_find_key_fp<kt>(hmap<kt> m, void* keyp);
  fixpoint int hmap_size_fp<kt>(hmap<kt> m);
  fixpoint int hmap_find_empty_fp<kt>(hmap<kt> m, int start);
  @*/

static
int find_key/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int start,
                         void* keyp, map_keys_equality* eq, int key_hash,
                         int capacity)
/*@ requires hmapping<kt>(?hm, ?kp, ?hsh, capacity, busybits, keyps, k_hashes) &*&
             kp(keyp, ?k) &*&
             hsh(k) == key_hash; @*/
/*@ ensures hmapping<kt>(hm, kp, hsh, capacity, busybits, keyps, k_hashes) &*&
            kp(keyp, k) &*&
            (hmap_exists_key_fp(hm, keyp) ?
             (result == hmap_find_key_fp(hm, keyp)) :
             (result == -1)); @*/
{
    int i = 0;
    for (; i < capacity; ++i)
    {
        int index = loop(start + i, capacity);
        int bb = busybits[index];
        int kh = k_hashes[index];
        void* kp = keyps[index];
        if (bb != 0 && kh == key_hash && eq(kp, keyp)) {
            return index;
        }
    }
    return -1;
}

static
int find_empty/*@ <kt> @*/(int* busybits, int start, int capacity)
/*@ requires hmapping<kt>(?hm, ?kp, ?hsh, capacity, busybits, ?keyps, ?k_hashes); @*/
/*@ ensures hmapping<kt>(hm, kp, hsh, capacity, busybits, keyps, k_hashes) &*&
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
                                int capacity) {
  (void)eq; (void)keyps; (void)khs; (void)vals;
  int i = 0;
  for (; i < capacity; ++i) {
    busybits[i] = 0;
  }
}

int map_get/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* values,
                        void* keyp, map_keys_equality* eq, int hash, int* value,
                        int capacity)
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
