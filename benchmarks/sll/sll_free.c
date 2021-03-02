#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void sll_free(loc x) {
if ((x == NULL)) {
return;
}
else {
int vx2 = READ_INT(x, 0);
loc nxtx2 = READ_LOC(x, 1);
sll_free(nxtx2);
free(x);
return;
}
}
