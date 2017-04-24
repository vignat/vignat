#ifndef _MAP_STUB_CONTROL_H_INCLUDED_
#define _MAP_STUB_CONTROL_H_INCLUDED_

#include "lib/containers/map.h"
#include "str-descr.h"

void map_set_layout(struct Map* map,
                    struct str_field_descr* key_fields,
                    int key_fields_count,
                    struct nested_field_descr* key_nests,
                    int nested_key_fields_count);

void map_reset(struct Map* map);

#endif//_MAP_STUB_CONTROL_H_INCLUDED_
