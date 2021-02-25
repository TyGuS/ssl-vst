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

        

void listmorph(loc x, loc r) {
if ((x == NULL)) {
return;
}
else {
int vx2 = READ_INT(x, 0);
loc nxtx2 = READ_LOC(x, 1);
listmorph(nxtx2, r);
loc y12 = READ_LOC(r, 0);
WRITE_LOC(x, 1, y12);
WRITE_LOC(r, 0, x);
return;
}
}
