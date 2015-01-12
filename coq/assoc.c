
#define SIZE (100)

//int mapping[SIZE];

int get(int* arr, int key)
{
    int rez = arr[key]; //using memory access (arr[key]) in an expression
    return rez; // (return ...) is forbidden by VST.
}

void set(int* arr, int key, int val)
{
    arr[key] = val;
}

