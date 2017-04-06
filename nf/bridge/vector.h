#ifndef _VECTOR_H_INCLUDED_
#define _VECTOR_H_INCLUDED_

#define VECTOR_CAPACITY_UPPER_LIMIT 140000

struct Vector;

int vector_allocate(int elem_size, int capacity,
                    struct Vector** vector_out);
void* vector_borrow(struct Vector* vector, int index);
void vector_return(struct Vector* vector, int index, void* value);

#endif//_VECTOR_H_INCLUDED_
