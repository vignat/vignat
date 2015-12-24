#ifndef _MAP_H_INCLUDED_
#define _MAP_H_INCLUDED_

#define MAP_CAPACITY (1024)

int get(int* busybits, void** keyps, int* k_hashes, int* values, void* keyp, int key_size);
int put(int* busybits, void** keyps, int* k_hashes, int* values, void* keyp, int key_size, int value);
int erase(int* busybits, void** keyps, int* key_hashes, void* keyp, int key_size);
int size(int* busybits);

#endif //_MAP_H_INCLUDED_
