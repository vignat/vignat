#include "include_ignored_by_verifast.h"
/**
   An auxilary header, defining the IGNORE macro to tell the compiler that a
   certain function parameter is not used.
*/
#ifdef _NO_VERIFAST_
#  define IGNORE(x) (void)(x)
#else //_NO_VERIFAST_
#  define IGNORE(x)
#endif //_NO_VERIFAST_
