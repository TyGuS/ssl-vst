#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



extern void sll_append(loc x1, loc ret);

void tree_flatten(loc z) {
loc x2 = READ_LOC(z, 0);
if ((x2 == NULL)) {
return;
}
else {
int vx22 = READ_INT(x2, 0);
loc lx22 = READ_LOC(x2, 1);
loc rx22 = READ_LOC(x2, 2);
WRITE_LOC(z, 0, lx22);
tree_flatten(z);
loc y12 = READ_LOC(z, 0);
WRITE_LOC(z, 0, rx22);
tree_flatten(z);
loc y22 = READ_LOC(z, 0);
sll_append(y12, z);
loc y32 = READ_LOC(z, 0);
loc y4 = (loc) malloc(2 * sizeof(loc));
free(x2);
WRITE_LOC(z, 0, y4);
WRITE_LOC(y4, 1, y32);
WRITE_INT(y4, 0, vx22);
return;
}
}
