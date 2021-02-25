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

        

void sll_append(loc x1, loc r) {
loc x22 = READ_LOC(r, 0);
if ((x1 == NULL)) {
return;
}
else {
int vx12 = READ_INT(x1, 0);
loc nxtx12 = READ_LOC(x1, 1);
sll_append(nxtx12, r);
loc y12 = READ_LOC(r, 0);
WRITE_LOC(x1, 1, y12);
WRITE_LOC(r, 0, x1);
return;
}
}
