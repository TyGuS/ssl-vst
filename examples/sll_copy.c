#include <stddef.h>

extern void free(void *p);
extern void *malloc(size_t size);

typedef union sslval {
  int ssl_int;
  void *ssl_ptr;
} *loc;
#define READ_LOC(x,y) (*(x+y)).ssl_ptr
#define READ_INT(x,y) (*(x+y)).ssl_int
#define WRITE_LOC(x,y,z) (*(x+y)).ssl_ptr = z
#define WRITE_INT(x,y,z) (*(x+y)).ssl_int = z

        

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
