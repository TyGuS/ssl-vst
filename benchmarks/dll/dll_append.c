#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void dll_append(loc x1, loc r) {
loc x22 = READ_LOC(r, 0);
if ((x1 == NULL)) {
return;
}
else {
int vx12 = READ_INT(x1, 0);
loc wx12 = READ_LOC(x1, 1);
loc a2 = READ_LOC(x1, 2);
dll_append(wx12, r);
loc y12 = READ_LOC(r, 0);
if ((y12 == NULL)) {
WRITE_LOC(x1, 1, NULL);
WRITE_LOC(r, 0, x1);
return;
}
else {
int vy122 = READ_INT(y12, 0);
loc wy122 = READ_LOC(y12, 1);
loc c12 = READ_LOC(y12, 2);
WRITE_LOC(y12, 2, x1);
WRITE_LOC(x1, 1, y12);
WRITE_LOC(r, 0, x1);
return;
}}
}
