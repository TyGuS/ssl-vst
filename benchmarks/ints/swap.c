#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void swap(loc x, loc y) {
loc a2 = READ_LOC(x, 0);
loc b2 = READ_LOC(y, 0);
WRITE_LOC(x, 0, b2);
WRITE_LOC(y, 0, a2);
return;

}
