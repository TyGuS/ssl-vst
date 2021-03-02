#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void tree_copy(loc r) {
loc x2 = READ_LOC(r, 0);
if ((x2 == NULL)) {
return;
}
else {
int vx22 = READ_INT(x2, 0);
loc lx22 = READ_LOC(x2, 1);
loc rx22 = READ_LOC(x2, 2);
WRITE_LOC(r, 0, lx22);
tree_copy(r);
loc y12 = READ_LOC(r, 0);
WRITE_LOC(r, 0, rx22);
tree_copy(r);
loc y22 = READ_LOC(r, 0);
loc y3 = (loc) malloc(3 * sizeof(loc));
WRITE_LOC(r, 0, y3);
WRITE_LOC(y3, 1, y12);
WRITE_LOC(y3, 2, y22);
WRITE_INT(y3, 0, vx22);
return;
}
}
