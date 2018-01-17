#include <iomanip>
#include <map>
#include <unordered_map>
#include <vector>
#include <string>
#include <chrono>
#include <iostream>
#include <glib.h>
#include "../vst/map/map.c"

#include "data.c"


using namespace std;
using namespace std::chrono;

enum dimensions
    {
        load5 = 0, load50 = 1, load95 = 2,
        gp003 = 0, gp1 = 1, gp30 = 2,
        hitr5 = 0, hitr50 = 1, hitr95 = 2
    };

void pretty_print(map<string, long> results[][3][3])
{
    for (int l = 0; l < 3; ++l)
    {
        for (int g = 0; g < 3; ++g)
            for (int h = 0; h < 3; ++h)
            {
                switch (l)
                {
                case 0: cout <<"load  5 "; break;
                case 1: cout <<"load 50 "; break;
                case 2: cout <<"load 95 "; break;
                };
                switch (g)
                {
                case 0: cout <<"30put->1get  "; break;
                case 1: cout <<" 1put->1get  "; break;
                case 2: cout <<" 1put->30get "; break;
                };
                switch (h)
                {
                case 0: cout <<"hitrate  5% "; break;
                case 1: cout <<"hitrate 50% "; break;
                case 2: cout <<"hitrate 95% "; break;
                };
                cout << " | c" <<setw(7) << results[l][g][h]["vst"]
                     << " | s" <<setw(7) << results[l][g][h]["stl"]
                     << " | g" <<setw(7) << results[l][g][h]["glib"] <<endl;
            }
        cout <<endl;
    }
}

void dump(map<string, long> results[][3][3])
{
    for (int l = 0; l < 3; ++l)
        for (int g = 0; g < 3; ++g)
            for (int h = 0; h < 3; ++h)
                cout << results[l][g][h]["vst"] <<"\n"
                     << results[l][g][h]["stl"] <<"\n"
                     << results[l][g][h]["glib"] <<endl;
}

int main(int argc, char** argv)
{
    const int count = 500;

    int keys[100];
    int busybits[100] = {};
    int values[100];
    unordered_map<int, int> m;
    GHashTable* hash = g_hash_table_new(g_int_hash, g_int_equal);

    map<string, long> results[3][3][3];

    high_resolution_clock::time_point t;

    t = high_resolution_clock::now();

#define REGISTER_MEASUREMENT(load, gp, hitr)                            \
    results[load][gp][hitr].insert(pair<string, long>                   \
                                   (NAME,                               \
                                    duration_cast<std::chrono::milliseconds> \
                                    ( high_resolution_clock::now() - t ).count()))
    
#define START_MEASUREMENT     t = high_resolution_clock::now()


#define NAME "vst"
#define PUT(k) (put(busybits, keys, values, k, 1))
#define GET(k) (get(busybits, keys, values, k))
#define ERASE(k) (erase(busybits, keys, k))
        #include "operations.c"
#undef PUT
#undef GET
#undef ERASE
#undef NAME


#define NAME "stl"
#define PUT(k) (m.insert(pair<int, int>(k, 1)))
#define GET(k) (m.find(k))
#define ERASE(k) (m.erase(k))
        #include "operations.c"
#undef PUT
#undef GET
#undef ERASE
#undef NAME

#define NAME "glib"
#define PUT(k) (g_hash_table_add(hash, &k))
#define GET(k) (g_hash_table_lookup(hash, &k))
#define ERASE(k) (g_hash_table_remove(hash, &k))
        #include "operations.c"
#undef PUT
#undef GET
#undef ERASE
#undef NAME

    if (argc > 1)
        dump(results);
    else
        pretty_print(results);
    g_hash_table_destroy(hash);

    return 0;
}
