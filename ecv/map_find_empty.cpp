/*-------------------------------------------------------*/
/* File:    /home/necto/proj/vnds/ecv/map_find_empty.cpp */
/* Author:  necto                                        */
/* Created: 09:36:43 on Tuesday September 22nd 2015 UTC  */
/*-------------------------------------------------------*/

#include "ecv.h"
#include "map.h"


int find_empty( int busybits[CAPACITY], int start)
   writes()
   pre(0 <= start; start < CAPACITY)
   pre(busybits.lim >= CAPACITY)
{
	assert((exists bb0 in 0..busybits.upb :- busybits[bb0] == 0) => (exists bbi in 0..busybits.upb :- busybits[bbi] == 0));
	assert((exists int bb0 :- 0 <= bb0 && bb0 < busybits.lim && busybits[bb0] == 0) => (exists int bbi :- 0 <= bbi && bbi < busybits.lim && busybits[loop(bbi)] == 0));
	assert((exists int bbi :- 0 <= bbi && bbi < busybits.lim && busybits[loop(bbi)] == 0) => (exists int bbi :- 5 <= bbi && bbi < busybits.lim + 5 && (busybits[loop(bbi)] == 0 || busybits[loop(bbi-CAPACITY)] == 0)));
	//assert(forall int bbi :- CAPACITY <= bbi && bbi < CAPACITY + 5 && busybits[loop(bbi-CAPACITY)] == 0 => busybits[loop(bbi)] == 0);
	assert(forall int bbi :- 0 <= bbi && bbi < 5 => loop(bbi + CAPACITY) == loop(bbi));
	assert(forall int bbi :- 0 <= bbi && bbi < 5 => loop(bbi + CAPACITY - CAPACITY) == loop(bbi + CAPACITY));
	assert(forall int bbi :- CAPACITY <= bbi && bbi < CAPACITY + 5 => loop(bbi - CAPACITY) == loop(bbi));
	//assert((exists bb0 in busybits.indices :- busybits[bb0] == 0) => (exists int bbi :- busybits[loop(bbi)] == 0));
	return 0;
}

#if 0

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
int find_empty (int busybits[CAPACITY], int start)
  writes()
  pre(0 <= start; start < CAPACITY)
  pre(busybits.lim >= CAPACITY)
{
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
	 
	//assert((exists bb0 in busybits.all :- bb0 == 0) => (exists integer bbi :- busybits[bbi] == bb0));
	assert((exists bb0 in busybits.indices :- busybits[bb0] == 0) => (exists integer bbi :- busybits[loop(bbi)] == 0));
	return 0;
	/*
    for (int i = 0; i < CAPACITY; ++i)
	  writes(i)
	  keep(0 <= i; i <= CAPACITY)
	  keep(0 <= start; start < CAPACITY)
	  keep((exists bb0 in busybits.all :- bb0 == 0) => (exists bbi in ((1 + start + i)..(1 + start + CAPACITY - 1)) :-
		   busybits[loop((int)bbi)] == 0))
	  decrease(CAPACITY - i)
	{
        int index = loop(1 + start + i);
        int bb = busybits[index];
        if (0 == bb) {
            return index;
        }
    }
    return -1;
*/
}

#endif
