#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void sll_copy(loc r) {
loc x2 = READ_LOC(r, 0);
if ((x2 == NULL)) {
return;
}
else {
int vx22 = READ_INT(x2, 0);
loc nxtx22 = READ_LOC(x2, 1);
WRITE_LOC(r, 0, nxtx22);
sll_copy(r);
loc y12 = READ_LOC(r, 0);
loc y2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(r, 0, y2);
WRITE_LOC(y2, 1, y12);
WRITE_INT(y2, 0, vx22);
return;
}
}
