
#define CAPACITY 1000000

/*@ logic integer loop_l(integer k) = (k%CAPACITY + CAPACITY)%CAPACITY;
 */

/*@ lemma loop_bijection: \forall integer k;
  @   0 <= k < CAPACITY ==> loop_l(k) == k;
*/
/*@ lemma loop_injection: \forall integer k;
  @   0 <= k ==> loop_l(k + CAPACITY) == loop_l(k);
*/

/*@ predicate full(int *busybits) = 
  @   \forall integer x; 0 <= x < CAPACITY ==> busybits[x] != 0;
*/

/*@ lemma non_full_exists: \forall int* busybits;
  @ !full(busybits) <==> (\exists integer x; 0 <= x < CAPACITY &&
  @                                          busybits[x] == 0);
*/

/*@ logic integer size_rec{L}(int* busybits, integer capa) = 
  @   (capa == 0) ? 0 :
  @   (busybits[capa-1] != 0) ? 1 + size_rec(busybits, capa - 1) :
  @    size_rec(busybits, capa - 1);
*/

/*@ lemma size_rec_on_zero: \forall int* busybits, integer capa;
  @   0 <= capa && busybits[capa] == 0 ==> 
  @     size_rec(busybits, capa + 1) == size_rec(busybits, capa);
  @
  @ lemma size_rec_on_one: \forall int* busybits, integer capa;
  @   0 <= capa && busybits[capa] != 0 ==>
  @     size_rec(busybits, capa + 1) == 1 + size_rec(busybits, capa);
*/

/*@ lemma size_rec_bounds: \forall int* busybits, integer capa;
  @   0 <= capa ==> 0 <= size_rec(busybits, capa) <= capa;
*/

/*@ logic boolean full_rec{L}(int *busybits, integer capa) = 
  @  (capa == 0) ? \true :
  @  (busybits[capa-1] != 0) ? full_rec(busybits, capa - 1) : \false;
  @
  @ lemma full_rec_full: \forall int* busybits;
  @   full_rec(busybits, CAPACITY) <==> full(busybits);
  @
  @ lemma full_rec_size_rec: \forall int* busybits, integer capa;
  @   capa >= 0 ==> (size_rec(busybits, capa) == capa <==> full_rec(busybits, capa));
*/

/*@ lemma size_rec_full: \forall int* busybits;
  @   full(busybits) <==> size_rec(busybits, CAPACITY) == CAPACITY;
*/

/*@ assigns \nothing;
  @ ensures 0 <= \result < CAPACITY;
  @ ensures \result == loop_l(k);
 */
int loop (int k)
{   
    //single "%" result ranges from -CAPACITY to CAPACITY.
    return (k%CAPACITY + CAPACITY)%CAPACITY;//ranges from 0 to CAPACITY.
}

/*@ requires 0 <= start < CAPACITY;
  @ requires \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ assigns \nothing;
  @ behavior non_full:
  @   assumes !full(busybits);
  @   ensures 0 <= \result < CAPACITY;
  @   ensures busybits[\result] == 0;
  @ behavior full:
  @   assumes full(busybits);
  @   ensures \result == -1;
*/
int find_empty (int busybits[CAPACITY], int start) {
    /*@ loop invariant \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
      @ loop invariant 0 <= i <= CAPACITY;
      @ loop invariant 0 <= start < CAPACITY;
      @ loop assigns i;
      @ for non_full: loop invariant
      @   \exists integer x; 0 <= x < CAPACITY && busybits[x] == 0;
      @ for non_full: loop invariant
      @   \exists integer x;
      @     1 + start + i <= x < 1 + start + CAPACITY &&
      @     busybits[loop_l(x)] == 0;
      @ for full: loop invariant
      @   \forall integer x; 0 <= x < CAPACITY ==> busybits[x] != 0;
      @ loop variant (CAPACITY - i);
     */
    for (int i = 0; i < CAPACITY; ++i) {
        int index = loop(1 + start + i);
        int bb = busybits[index];
        if (0 == bb) {
            return index;
        }
    }
    return -1;
}

/*@ predicate has_K(int *busybits, int *keys, int k) = \exists integer x;
  @   0 <= x < CAPACITY && busybits[x] != 0 && keys[x] == k;
*/

/*@ requires 0 <= start < CAPACITY;
  @ requires \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ requires \valid(keys + {i | integer i; 0 <= i < CAPACITY});
  @ assigns \nothing;
  @ behavior has:
  @   assumes has_K(busybits, keys, key);
  @   ensures 0 <= \result < CAPACITY;
  @   ensures busybits[\result] != 0;
  @   ensures keys[\result] == key;
  @ behavior has_not:
  @   assumes !has_K(busybits, keys, key);
  @   ensures \result == -1;
*/
int find_key (int busybits[CAPACITY], int keys[CAPACITY], int start, int key) {
    /*@ loop invariant \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
      @ loop invariant \valid(keys + {i | integer i; 0 <= i < CAPACITY});
      @ loop invariant 0 <= i <= CAPACITY;
      @ loop invariant 0 <= start < CAPACITY;
      @ loop assigns i;
      @ for has: loop invariant has_K(busybits, keys, key);
      @ for has: loop invariant
      @   \exists integer x;
      @     1 + start + i <= x < 1 + start + CAPACITY &&
      @     busybits[loop_l(x)] != 0 && keys[loop_l(x)] == key;
      @ for has_not: loop invariant
      @   \forall integer x; 0 <= x < CAPACITY ==>
      @      busybits[x] == 0 || keys[x] != key;
      @ loop variant (CAPACITY - i);
     */
    for (int i = 0; i < CAPACITY; ++i) {
        int index = loop(1 + start + i);
        int bb = busybits[index];
        int k = keys[index];
        if (bb != 0) {
            if (k == key) {
                return index;
            }
            //@ assert(keys[index] != key);
            //@ assert(busybits[index] != 0);
        }
        //@ assert(busybits[index] == 0 || \
                   (busybits[index] != 0 && keys[index] != key));
    }
    return -1;
}

/*@ predicate has_KV(int* busybits, int* keys, int* values, int key, int value) =
  @   \exists integer x; 0 <= x < CAPACITY && busybits[x] != 0 &&
  @             keys[x] == key && values[x] == value;
*/

/*@ requires \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ requires \valid(keys + {i | integer i; 0 <= i < CAPACITY});
  @ requires \valid(values + {i | integer i; 0 <= i < CAPACITY});
  @ assigns \nothing;
  @ behavior has:
  @   assumes has_K(busybits, keys, key);
  @   ensures has_KV(busybits, keys, values, key, \result);
  @ behavior has_not:
  @   assumes !has_K(busybits, keys, key);
  @   ensures \result == -1;
*/
int get(int busybits[CAPACITY], int keys[CAPACITY], int values[CAPACITY], int key)
{
    int start = loop(key);
    int index = find_key(busybits, keys, start, key);

    if (-1 == index)
    {
        return -1;
    }
    int val = values[index];
    return val;
}

/*@ predicate no_doubles(int* busybits, int* keys) = \forall integer x,y;
  @   0 <= x < CAPACITY && 0 <= y < CAPACITY && x != y &&
  @   busybits[x] != 0 && busybits[y] != 0 ==>
  @   keys[x] != keys[y];
*/

/*@ requires \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ requires \valid(keys + {i | integer i; 0 <= i < CAPACITY});
  @ requires \valid(values + {i | integer i; 0 <= i < CAPACITY});
  @ requires \separated((busybits + {i | integer i; 0 <= i < CAPACITY}),
                        (keys + {i | integer i; 0 <= i < CAPACITY}));
  @ requires \separated((values + {i | integer i; 0 <= i < CAPACITY}),
                        (keys + {i | integer i; 0 <= i < CAPACITY}));
  @ requires \separated((busybits + {i | integer i; 0 <= i < CAPACITY}),
                        (values + {i | integer i; 0 <= i < CAPACITY}));
  @ assigns *(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ assigns *(keys + {i | integer i; 0 <= i < CAPACITY});
  @ assigns *(values + {i | integer i; 0 <= i < CAPACITY});
  @ ensures \forall int k, int v;
  @   has_KV(\old(busybits), \old(keys), \old(values), k, v) ==>
  @   has_KV(busybits, keys, values, k, v);
  @ behavior non_full:
  @   assumes !full(busybits);
  @   ensures has_KV(busybits, keys, values, key, value);
  @   ensures \result == 0;
  @   ensures size_rec(\old(busybits), CAPACITY) + 1 == size_rec(busybits, CAPACITY);
  @ behavior full:
  @   assumes full(busybits);
  @   assigns \nothing;
  @   ensures \result == -1;
*/
int put(int busybits[CAPACITY], int keys[CAPACITY], int values[CAPACITY], int key, int value)
{
    int start = loop(key);
    int index = find_empty(busybits, start);

    if (-1 == index)
    {
        return -1;
    }
    //@ assert(busybits[index] == 0);
    busybits[index] = 1;
    //@ assert(busybits[index] != 0);
    keys    [index] = key;
    //@ assert(keys[index] == key);
    //@ assert(busybits[index] != 0);
    values  [index] = value;
    //@ assert(busybits[index] != 0);
    //@ assert(keys[index] == key);
    //@ assert(values[index] == value);
    return 0;
}

/*@ requires \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ requires \valid(keys + {i | integer i; 0 <= i < CAPACITY});
  @ requires \separated((busybits + {i | integer i; 0 <= i < CAPACITY}),
                        (keys + {i | integer i; 0 <= i < CAPACITY}));
  @ requires no_doubles(busybits, keys);
  @ assigns *(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ behavior has:
  @   assumes has_K(busybits, keys, key);
  @   ensures !full(busybits);
  @   ensures !has_K(busybits, keys, key);
  @   ensures \result == 0;
  @   //Not only it preserves all the keys, it also keeps them
  @   //on place (important for corresponding values).
  @   ensures \forall integer i, int k; 0 <= i < CAPACITY &&
  @     \old(busybits)[i] != 0 && \old(keys)[i] == k && k != key ==>
  @     busybits[i] != 0 && keys[i] == k;
  @ behavior has_not:
  @   assumes !has_K(busybits, keys, key);
  @   assigns \nothing;
  @   ensures \result == -1;
*/
int erase(int busybits[CAPACITY], int keys[CAPACITY], int key)
{
    int start = loop(key);
    int index = find_key(busybits, keys, start, key);

    if (-1 == index)
    {
        return -1;
    }
    busybits[index] = 0;
    return 0;
}

/*@ requires \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
  @ assigns \nothing;
  @ ensures 0 <= \result <= CAPACITY;
  @ ensures \result == size_rec{Here}(busybits, CAPACITY);
*/
int size(int busybits[CAPACITY]) {
    int i = 0;
    int s = 0;
    /*@ loop invariant \valid(busybits + {i | integer i; 0 <= i < CAPACITY});
      @ loop invariant 0 <= i <= CAPACITY;
      @ loop invariant 0 <= s <= i;
      @ loop invariant s == size_rec(busybits, i);
      @ loop assigns i, s;
      @ loop variant (CAPACITY - i);
    */
    for (i = 0; i < CAPACITY; ++i) {
        //@ assert(s == size_rec(busybits, i));
        int bb = busybits[i];
        if (bb != 0) {
            //@ assert(s == size_rec(busybits, i));
            //@ assert(busybits[i] != 0);
            //@ assert(size_rec(busybits, i + 1) == 1 + size_rec(busybits, i));
            ++s;
            //@ assert(s == size_rec(busybits, i + 1));
        } else {
            //@ assert(busybits[i] == 0);
            //@ assert(size_rec(busybits, i + 1) == size_rec(busybits, i));
        }
        //@ assert(s == size_rec(busybits, i + 1));
        //@ assert(i < CAPACITY);
    }
    //@ assert( i == CAPACITY);
    //@ assert( s <= CAPACITY);
    return s;
}


