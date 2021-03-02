#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void sll_append(loc x1, loc r) {
loc x22 = READ_LOC(r, 0);
if ((x1 == NULL)) {
return;
}
else {
int vx12 = READ_INT(x1, 0);
loc nxtx12 = READ_LOC(x1, 1);
sll_append(nxtx12, r);
loc y12 = READ_LOC(r, 0);
WRITE_LOC(x1, 1, y12);
WRITE_LOC(r, 0, x1);
return;
}
}
