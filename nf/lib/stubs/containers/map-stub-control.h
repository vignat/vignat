#ifndef _MAP_STUB_CONTROL_H_INCLUDED_
#define _MAP_STUB_CONTROL_H_INCLUDED_

#include "str-descr.h"

void map_set_layout(struct Map* map,
                    struct str_field_descr* key_fields,
                    int key_fields_count);

#endif//_MAP_STUB_CONTROL_H_INCLUDED_
