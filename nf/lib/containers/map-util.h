#ifndef _MAP_UTIL_H_INCLUDED_
#define _MAP_UTIL_H_INCLUDED_

#define CAPACITY_UPPER_LIMIT 140000

typedef int map_key_hash/*@ <K>(predicate (void*; K) keyp,
                                fixpoint (K,int) hash) @*/(void* k1);
//@ requires [?fr]keyp(k1, ?kk1);
//@ ensures [fr]keyp(k1, kk1) &*& result == hash(kk1);

#endif//_MAP_UTIL_H_INCLUDED_
