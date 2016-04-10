#ifndef _MAP_H_INCLUDED_
#define _MAP_H_INCLUDED_

typedef int map_keys_equality/*@<K>(predicate (void*, K) keyp) @*/(void* k1, void* k2);
//@ requires keyp(k1, ?kk1) &*& keyp(k2, ?kk2);
//@ ensures keyp(k1, kk1) &*& keyp(k2, kk2) &*& (0 == result ? (kk1 != kk2) : (kk1 == kk2));


/*@ predicate pred_arg4<t1,t2,t3,t4>(predicate (t1,t2,t3,t4) p) = true;
    predicate pred_arg2<t1,t2>(predicate (t1,t2) p) = true;
  @*/

/*@
  inductive map<kt> = dmap(list<kt>, list<int>);

  predicate mapping<kt>(map<kt> m,
                        predicate (void*, kt) keyp,
                        predicate (kt,int) recp,
                        fixpoint (kt,int) hash,
                        int capacity,
                        int* busybits,
                        void** keyps,
                        int* k_hashts,
                        int* values);

  fixpoint map<kt> empty_map_fp<kt>();
  fixpoint int map_get_fp<kt>(map<kt> m, kt key);
  fixpoint bool map_has_fp<kt>(map<kt> m, kt key);
  fixpoint map<kt> map_put_fp<kt>(map<kt> m, kt key, int val);
  fixpoint map<kt> map_erase_fp<kt>(map<kt> m, kt key);
  fixpoint int map_size_fp<kt>(map<kt> m);
  @*/

/**
 * Values and keys are void*, and the actual keys and values should be managed
 * by the client application.
 *
 * I could not use integer keys, because need to operate with keys like
 * int_key/ext_key that are much bigger than a 32bit integer.
 */
void map_initialize/*@ <kt> @*/ (int* busybits, map_keys_equality* cmp,
                                 int capacity);
/*@ requires exists<kt>(_) &*&
             exists<fixpoint (kt,int)>(?hash) &*&
             [_]is_map_keys_equality<kt>(cmp, ?keyp) &*&
             pred_arg2<kt, int>(?recp) &*&
             ints(busybits, capacity, ?bbs) &*&
             pointers(?keyps, capacity, ?kplist) &*&
             ints(?vals, capacity, ?vallist) &*&
             ints(?khs, capacity, ?khlist); @*/
/*@ ensures mapping<kt>(empty_map_fp(), keyp, recp, hash,
                        capacity, busybits, keyps,
                        khs, vals); @*/

int map_get/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* values,
                        void* keyp, map_keys_equality* eq, int hash, int* value,
                        int capacity);
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

int map_put/*@ <kt> @*/(int* busybits, void** keyps, int* k_hashes, int* values,
                        void* keyp, int hash, int value,
                        int capacity);
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

int map_erase/*@ <kt> @*/(int* busybits, void** keyps, int* key_hashes,
                          void* keyp, map_keys_equality* eq, int hash,
                          int capacity);
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         keyps, key_hashes, ?values) &*&
             kp(keyp, ?k) &*&
             hsh(k) == hash; @*/
/*@ ensures kp(keyp, k) &*&
            (map_has_fp(m, k) ?
             (result == 1 &*&
              mapping<kt>(map_erase_fp(m, k), kp, recp, hsh,
                          capacity, busybits, keyps, key_hashes, values)) :
             (result == 0 &*&
              mapping<kt>(m, kp, recp, hsh,
                          capacity, busybits, keyps, key_hashes, values))); @*/

int map_size/*@ <kt> @*/(int* busybits, int capacity);
/*@ requires mapping<kt>(?m, ?kp, ?recp, ?hsh, capacity, busybits,
                         ?keyps, ?k_hashes, ?values); @*/
/*@ ensures mapping<kt>(m, kp, recp, hsh, capacity, busybits,
                        keyps, k_hashes, values) &*&
            result == map_size_fp(m);@*/

#endif //_MAP_H_INCLUDED_
