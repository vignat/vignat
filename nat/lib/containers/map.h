#ifndef _MAP_H_INCLUDED_
#define _MAP_H_INCLUDED_

//#define MAP_CAPACITY (1024)

typedef int map_keys_equality(void* k1, void* k2);

void map_initialize(int* busybits, map_keys_equality* cmp, int capacity);
/**
 * All arrays must contain at least MAP_CAPACITY number of cells.
 * Values and keys are void*, and the actual keys and values should be managed
 * by the client application.
 *
 * I could not use integer keys, because need to operate with keys like
 * int_key/ext_key that are much bigger than a 32bit integer.
 */
int map_get(int* busybits, void** keyps, int* k_hashes, int* values,
            void* keyp, map_keys_equality* eq, int hash, int* value,
            int capacity);
int map_put(int* busybits, void** keyps, int* k_hashes, int* values,
            void* keyp, int hash, int value,
            int capacity);
int map_erase(int* busybits, void** keyps, int* key_hashes,
              void* keyp, map_keys_equality* eq, int hash,
              int capacity);
int map_size(int* busybits, int capacity);

#endif //_MAP_H_INCLUDED_
