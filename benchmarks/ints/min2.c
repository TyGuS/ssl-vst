#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void min2(loc r, int x, int y) {
if ((x <= y)) {
WRITE_INT(r, 0, x);
return;
} else {
WRITE_INT(r, 0, y);
return;
}
}
