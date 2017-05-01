#ifndef _VECTOR_STUB_CONTROL_H_INCLUDED_
#define _VECTOR_STUB_CONTROL_H_INCLUDED_

#include "lib/containers/vector.h"
#include "str-descr.h"

void vector_set_layout(struct Vector* vector,
                       struct str_field_descr* value_fields,
                       int field_count,
                       struct nested_field_descr* val_nest_fields,
                       int nest_field_count,
                       char* type_tag);

void vector_reset(struct Vector* vector);

#endif// _VECTOR_STUB_CONTROL_H_INCLUDED_
