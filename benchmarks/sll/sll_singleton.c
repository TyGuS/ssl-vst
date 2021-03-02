#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void sll_singleton(int x, loc p) {
loc a2 = READ_LOC(p, 0);
loc y2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(p, 0, y2);
WRITE_LOC(y2, 1, NULL);
WRITE_INT(y2, 0, x);
return;

}
