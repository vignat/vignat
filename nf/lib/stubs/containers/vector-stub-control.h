#ifndef _VECTOR_STUB_CONTROL_H_INCLUDED_
#define _VECTOR_STUB_CONTROL_H_INCLUDED_

#include "lib/containers/vector.h"
#include "str-descr.h"

void vector_set_layout(struct Vector* vector,
                       struct str_field_descr* value_fields,
                       int field_count);

void vector_reset(struct Vector* vector);

#endif// _VECTOR_STUB_CONTROL_H_INCLUDED_
