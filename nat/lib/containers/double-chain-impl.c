#include "double-chain-impl.h"

enum DCHAIN_ENUM {
    ALLOC_LIST_HEAD = 0,
    FREE_LIST_HEAD = 1,
    INDEX_SHIFT = DCHAIN_RESERVED
};


void dchain_impl_init(struct dchain_cell *cells, int size) {
    cells[ALLOC_LIST_HEAD].prev = 0;
    cells[ALLOC_LIST_HEAD].next = 0;
    int i = INDEX_SHIFT;
    cells[FREE_LIST_HEAD].next = i;
    cells[FREE_LIST_HEAD].prev = cells[FREE_LIST_HEAD].next;
    while (i < (size + INDEX_SHIFT - 1)) {
        cells[i].next = i+1;
        cells[i].prev = cells[i].next;
        ++i;
    }
    cells[i].next = FREE_LIST_HEAD;
    cells[i].prev = cells[i].next;
}

int dchain_impl_allocate_new_index(struct dchain_cell *cells, int *index) {
    /* No more empty cells. */
    if (cells[FREE_LIST_HEAD].next == FREE_LIST_HEAD)
        return 0;
    int allocated = cells[FREE_LIST_HEAD].next;
    /* Extract the link from the "empty" chain. */
    cells[FREE_LIST_HEAD].next = cells[allocated].next;
    
    /* Add the link to the "new"-end "alloc" chain. */
    cells[allocated].next = ALLOC_LIST_HEAD;
    cells[allocated].prev = cells[ALLOC_LIST_HEAD].prev;
    cells[cells[ALLOC_LIST_HEAD].prev].next = allocated;
    cells[ALLOC_LIST_HEAD].prev = allocated;

    *index = allocated - INDEX_SHIFT;
    return 1;
}

int dchain_impl_free_index(struct dchain_cell *cells, int index) {
    int freed = index + INDEX_SHIFT;
    /* The index is already free. */
    if (cells[freed].next == cells[freed].prev)
        return 0;
    /* Extract the link from the "alloc" chain. */
    cells[cells[freed].prev].next = cells[freed].next;
    cells[cells[freed].next].prev = cells[freed].prev;

    /* Add the link to the "free" chain. */
    cells[freed].next = cells[FREE_LIST_HEAD].next;
    cells[freed].prev = cells[freed].next;
    cells[FREE_LIST_HEAD].next = freed;
    cells[FREE_LIST_HEAD].prev = cells[FREE_LIST_HEAD].next;
    return 1;
}

int dchain_impl_get_oldest_index(struct dchain_cell *cells, int *index) {
    /* No allocated indexes. */
    if (cells[ALLOC_LIST_HEAD].next == cells[ALLOC_LIST_HEAD].prev)
        return 0;
    *index = cells[ALLOC_LIST_HEAD].next - INDEX_SHIFT;
    return 1;
}

int dchain_impl_rejuvenate_index(struct dchain_cell *cells, int index) {
    int lifted = index + INDEX_SHIFT;
    /* The index is not allocated. */
    if (cells[lifted].next == cells[lifted].prev)
        return 0;
    
    /* Unlink it from the middle of the "alloc" chain. */
    cells[cells[lifted].prev].next = cells[lifted].next;
    cells[cells[lifted].next].prev = cells[lifted].prev;

    /* Link it at the very end - right before the special link. */
    cells[lifted].next = ALLOC_LIST_HEAD;
    cells[lifted].prev = cells[ALLOC_LIST_HEAD].prev;
    cells[cells[ALLOC_LIST_HEAD].prev].next = lifted;
    cells[ALLOC_LIST_HEAD].prev = lifted;
    return 1;
}

