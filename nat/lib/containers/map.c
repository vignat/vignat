#include <stdint.h>
#include <string.h>

#include "map.h"

static
int loop(int k, int capacity)
{
    int g = k%capacity;
    int res = (g + capacity)%capacity;
    return res;
}

//TODO: introduce the "chain continuation" bit to optimize search for abscent.

static
int find_key(int* busybits, void** keyps, int* k_hashes, int start,
             void* keyp, map_keys_equality* eq, int key_hash,
             int capacity)
{
    int i = 0;
    for (; i < capacity; ++i)
    {
        int index = loop(start + i, capacity);
        int bb = busybits[index];
        int kh = k_hashes[index];
        void* kp = keyps[index];
        if (bb != 0 && kh == key_hash && eq(kp, keyp)) {
            return index;
        }
    }
    return -1;
}

static
int find_empty(int* busybits, int start, int capacity)
{
    int i = 0;
    for (; i < capacity; ++i)
    {
        int index = loop(start + i, capacity);
        int bb = busybits[index];
        if (0 == bb) {
            return index;
        }
    }
    return -1;
}

void map_initialize(int* busybits, map_keys_equality* eq, int capacity) {
  (void)eq;
  int i = 0;
  for (; i < capacity; ++i) {
    busybits[i] = 0;
  }
}

int map_get(int* busybits, void** keyps, int* k_hashes, int* values,
            void* keyp, map_keys_equality* eq, int hash, int* value,
            int capacity)
{
    int start = loop(hash, capacity);
    int index = find_key(busybits, keyps, k_hashes, start,
                         keyp, eq, hash, capacity);
    if (-1 == index)
    {
        return 0;
    }
    *value = values[index];
    return 1;
}

int map_put(int* busybits, void** keyps, int* k_hashes, int* values,
            void* keyp, int hash, int value,
            int capacity)
{
    int start = loop(hash, capacity);
    int index = find_empty(busybits, start, capacity);

    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 1;
    keyps[index] = keyp;
    k_hashes[index] = hash;
    values[index] = value;
    return 1;
}

int map_erase(int* busybits, void** keyps, int* k_hashes, void* keyp,
              map_keys_equality* eq, int hash, int capacity)
{
    int start = loop(hash, capacity);
    int index = find_key(busybits, keyps, k_hashes, start,
                         keyp, eq, hash, capacity);
    if (-1 == index)
    {
        return 0;
    }
    busybits[index] = 0;
    return 1;
}

int map_size(int* busybits, int capacity)
{
    int s = 0;
    int i = 0;
    for (; i < capacity; ++i)
    {
        if (busybits[i] != 0)
        {
            ++s;
        }
    }
    return s;
}
