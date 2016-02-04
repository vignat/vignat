#ifndef _MAP_H_INCLUDED_
#define _MAP_H_INCLUDED_

#define MAP_CAPACITY (1024)

/**
 * All arrays must contain at least MAP_CAPACITY number of cells.
 * Values and keys are void*, and the actual keys and values should be managed
 * by the client application.
 *
 * I could not use integer keys, because need to operate with keys like
 * int_key/ext_key that are much bigger than a 32bit integer.
 */
int get(int* busybits, void** keyps, int* k_hashes, int* values,
        void* keyp, int key_size, int* value);
int put(int* busybits, void** keyps, int* k_hashes, int* values,
        void* keyp, int key_size, int value);
int erase(int* busybits, void** keyps, int* key_hashes,
          void* keyp, int key_size);
int size(int* busybits);

#endif //_MAP_H_INCLUDED_
