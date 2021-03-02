#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void sll_max(loc x, loc r) {
loc a2 = READ_LOC(r, 0);
if ((x == NULL)) {
WRITE_INT(r, 0, 0);
return;
}
else {
int vx2 = READ_INT(x, 0);
loc nxtx2 = READ_LOC(x, 1);
sll_max(nxtx2, r);
int hi1x2 = READ_INT(r, 0);
WRITE_INT(r, 0, ((hi1x2 <= vx2) ? vx2 : hi1x2));
return;
}
}
