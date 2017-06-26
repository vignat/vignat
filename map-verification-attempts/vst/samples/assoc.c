
int get(int* arr, int key)
{
    int rez = arr[key]; //using memory access (arr[key]) in an expression
    return rez; // (return ...) is forbidden by VST.
}

void set(int* arr, int key, int val)
{
    arr[key] = val;
}

int hash(int key)
{
    if (key < 0)
        return key%100 + 99;
    return key%100;
}

int cGet(int* arr, int key)
{
    int h = hash(key);
    return get(arr, h);
}

void cSet(int* arr, int key, int val)
{
    int h = hash(key);
    set(arr, h, val);
}
