#include <stdlib.h>

#include "double-chain.h"
#include "double-chain-impl.h"

struct dchain_cell *cells = NULL;

int dchain_allocate(int index_range) {
    if (NULL == (cells = malloc(sizeof(struct dchain_cell)*
                                (index_range + DCHAIN_RESERVED))))
        return 0;
    dchain_impl_init(cells, index_range);
    return 1;
}

int dchain_allocate_new_index(int *index) {
    return dchain_impl_allocate_new_index(cells, index);
}

int dchain_free_index(int index) {
    return dchain_impl_free_index(cells, index);
}

int dchain_get_oldest_index(int *index) {
    return dchain_impl_get_oldest_index(cells, index);
}

int dchain_rejuvenate_index(int index) {
    return dchain_impl_rejuvenate_index(cells, index);
}
