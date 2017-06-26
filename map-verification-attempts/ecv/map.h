/*-------------------------------------------------------*/
/* File:    /home/necto/proj/vnds/ecv/map.h              */
/* Author:  necto                                        */
/* Created: 09:35:21 on Tuesday September 22nd 2015 UTC  */
/*-------------------------------------------------------*/

#include "ecv.h"


#define CAPACITY 100

int loop (int k)
  writes()
  post(0 <= result; result < CAPACITY)
  post((0 <= k && k < CAPACITY) => result == k)
  post(0 <= k && k < maxof(int) => result == k%CAPACITY);
  
assume(forall int k :- 0 <= k && k < (maxof(int) - CAPACITY) => loop(k + CAPACITY) == loop(k));
assert(forall k in 0..(CAPACITY-1) :- loop(k) == k);
assume(forall k in 0..(CAPACITY-1) :- (exists int x :- loop(x) == k));

/*  
int find_empty (int busybits[CAPACITY], int start)
  writes()
  pre(0 <= start; start < CAPACITY)
  pre(busybits.lim >= CAPACITY)
  post(exists bb in busybits.all :- bb == 0 => 0 <= result && result < CAPACITY && busybits[result] == 0)
  post(forall bb in busybits.all :- bb != 0 => result == -1);
*/
  
int find_key (int busybits[CAPACITY], int keys[CAPACITY], int start, int key)
  writes()
  pre(busybits.lim >= CAPACITY)
  pre(keys.lim >= CAPACITY)
  pre(0 <= start; start < CAPACITY)
  post((exists integer x :- 0 <= x && x < CAPACITY && busybits[x] != 0 && keys[x] == key) =>
       0 <= result && result < CAPACITY && busybits[result] != 0 && keys[result] == key)
  post((forall integer x :- 0 <= x && x < CAPACITY => busybits[x] == 0 || keys[x] != key) =>
       result == -1);
	   
