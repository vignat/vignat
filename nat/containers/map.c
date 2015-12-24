#include <stdint.h>
#include <string.h>

#include "map.h"

static
int loop (int k)
{
    int g = k%MAP_CAPACITY;
    int res = (g + MAP_CAPACITY)%MAP_CAPACITY;
    return res;
}

//TODO: introduce the "chain continuation" bit to optimize search for abscent.

static
uint32_t hash (void* key, int key_size)
{
    uint32_t* slice = (uint32_t*)key;
    int n = key_size*sizeof(uint8_t)/sizeof(uint32_t);
    uint32_t rez = 0;
    for (--n; n >= 0; --n)
    {
        rez ^= slice[n];
    }
    return rez;
}

static
int find_key(int* busybits, void** keyps, int* k_hashes, int start, void* keyp, int key_size, int key_hash)
{
    int i = 0;
    for (; i < MAP_CAPACITY; ++i)
    {
        int index = loop(start + i);
        int bb = busybits[index];
        int kh = k_hashes[index];
        void* kp = keyps[index];
        if (bb != 0 && kh == key_hash && 0 == memcmp(kp, keyp, key_size)) {
            return index;
        }
    }
    return -1;
}

static
int find_empty (int* busybits, int start)
{
    int i = 0;
    for (; i < MAP_CAPACITY; ++i)
    {
        int index = loop(start + i);
        int bb = busybits[index];
        if (0 == bb) {
            return index;
        }
    }
    return -1;
}

int get(int* busybits, void** keyps, int* k_hashes, int* values, void* keyp, int key_size, int* value)
{
    int h = hash(keyp, key_size);
    int start = loop(h);
    int index = find_key(busybits, keyps, k_hashes, start, keyp, key_size, h);

    if (-1 == index)
    {   
        return 0;
    }
    *value = values[index];
    return 1;
}

int put(int* busybits, void** keyps, int* k_hashes, int* values, void* keyp, int key_size, int value)
{
    int h = hash(keyp, key_size);
    int start = loop(h);
    int index = find_empty(busybits, start);

    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 1;
    keyps[index] = keyp;
    k_hashes[index] = h;
    values[index] = value;
    return 1;
}

int erase(int* busybits, void** keyps, int* k_hashes, void* keyp, int key_size)
{
    int h = hash(keyp, key_size);
    int start = loop(h);
    int index = find_key(busybits, keyps, k_hashes, start, keyp, key_size, h);

    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 0;
    return 1;
}

int size(int* busybits)
{
    int s = 0;
    int i = 0;
    for (; i < MAP_CAPACITY; ++i)
    {
        if (busybits[i] != 0)
        {
            ++s;
        }
    }
    return s;
}
