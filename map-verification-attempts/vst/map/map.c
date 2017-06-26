
int loop (int k)
{   //single "%" result ranges from -99 to 99.
    return (k%100 + 100)%100;//ranges from 0 to 99.
}

int find_empty (int* busybits, int start, int i)
{
    int index = loop(1 + start + i);
    int bb = busybits[index];

    if (0 == bb)
    {
        return index;
    }
    if (0 == i)
    {
        return -1;
    }
    return find_empty(busybits, start, i - 1);
}

int find_key (int* busybits, int* keys, int start, int key, int i)
{
    int index = loop(1 + start + i);
    int bb = busybits[index];
    int k = keys[index];

    if (1 == bb)
    {
        if (k == key)
        {
            return index;
        }
    }
    if (i == 0)
    {
        return -1;
    }
    return find_key(busybits, keys, start, key, i - 1);
}

int get(int* busybits, int* keys, int* values, int key)
{
    int start = loop(key);
    int index = find_key(busybits, keys, start, key, 99);

    if (-1 == index)
    {
        return -1;
    }
    int val = values[index];
    return val;
}

int put(int* busybits, int* keys, int* values, int key, int value)
{
    int start = loop(key);
    int index = find_empty(busybits, start, 99);

    if (-1 == index)
    {
        return -1;
    }
    busybits[index] = 1;
    keys    [index] = key;
    values  [index] = value;
    return 0;
}

int erase(int* busybits, int* keys, int key)
{
    int start = loop(key);
    int index = find_key(busybits, keys, start, key, 99);

    if (-1 == index)
    {
        return -1;
    }
    busybits[index] = 0;
    return 0;
}

int size_rec(int* busybits, int i)
{
    if (0 == i)
    {
        return 0;
    }
    int index = i - 1;
    int bb = busybits[index];

    if (1 == bb)
    {
        return 1 + size_rec(busybits, i - 1);
    }
    return size_rec(busybits, i - 1);
}

int size(int* busybits)
{
    return size_rec(busybits, 100);
}
