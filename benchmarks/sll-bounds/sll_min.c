#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void sll_min(loc x, loc r) {
loc a2 = READ_LOC(r, 0);
if ((x == NULL)) {
WRITE_INT(r, 0, 7);
return;
}
else {
int vx2 = READ_INT(x, 0);
loc nxtx2 = READ_LOC(x, 1);
sll_min(nxtx2, r);
int lo1x2 = READ_INT(r, 0);
WRITE_INT(r, 0, ((vx2 <= lo1x2) ? vx2 : lo1x2));
return;
}
}
