#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void sll_dupleton(int x, int y, loc r) {
loc a2 = READ_LOC(r, 0);
loc z2 = (loc) malloc(2 * sizeof(loc));
loc nxtz2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(r, 0, z2);
WRITE_LOC(z2, 1, nxtz2);
WRITE_LOC(nxtz2, 1, NULL);
WRITE_INT(z2, 0, x);
WRITE_INT(nxtz2, 0, y);
return;

}
