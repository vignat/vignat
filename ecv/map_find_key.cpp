/*-------------------------------------------------------*/
/* File:    /home/necto/proj/vnds/ecv/map_find_key.cpp   */
/* Author:  necto                                        */
/* Created: 09:36:52 on Tuesday September 22nd 2015 UTC  */
/*-------------------------------------------------------*/

#include "ecv.h"
#include "map.h"



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
int find_key (int busybits[CAPACITY], int keys[CAPACITY], int start, int key)
{
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
    for (int i = 0; i < CAPACITY; ++i)
	  writes(i)
	  keep(0 <= i; i <= CAPACITY)
	  keep(0 <= start; start < CAPACITY)
	  keep((exists integer x :- 0 <= x && x < CAPACITY && busybits[x] != 0 && keys[x] == key) =>
		   (exists xi in ((1 + start + i)..(1 + start + CAPACITY - 1)) :- busybits[loop((int)xi)] != 0 &&
																		   keys[loop((int)xi)] == key))
	  decrease(CAPACITY - i)
	{
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
