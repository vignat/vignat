#ifndef _STR_DESCR_H_INCLUDED_
#define _STR_DESCR_H_INCLUDED_

struct str_field_descr {
  int offset;
  int width;
  char* name;
};

struct nested_field_descr {
  int base_offset;
  int offset;
  int width;
  char *name;
};

#endif//_STR_DESCR_H_INCLUDED_
