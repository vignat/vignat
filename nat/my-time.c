#include <time.h>
#include "my-time.h"

uint32_t current_time(void) {
    return time(NULL);
}
