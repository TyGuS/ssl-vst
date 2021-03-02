#include <stddef.h>
#include "common.h"

extern void free(void *p);
extern void *malloc(size_t size);



        

void dll_singleton(int x, loc r) {
loc a2 = READ_LOC(r, 0);
loc y2 = (loc) malloc(3 * sizeof(loc));
WRITE_LOC(r, 0, y2);
WRITE_LOC(y2, 1, NULL);
WRITE_LOC(y2, 2, NULL);
WRITE_INT(y2, 0, x);
return;

}
