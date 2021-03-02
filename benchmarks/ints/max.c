#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void max(loc r, int x, int y) {
if ((y <= x)) {
WRITE_INT(r, 0, x);
return;
} else {
WRITE_INT(r, 0, y);
return;
}
}
