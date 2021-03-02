#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void tree_free(loc x) {
if ((x == NULL)) {
return;
}
else {
int vx2 = READ_INT(x, 0);
loc lx2 = READ_LOC(x, 1);
loc rx2 = READ_LOC(x, 2);
tree_free(lx2);
tree_free(rx2);
free(x);
return;
}
}
