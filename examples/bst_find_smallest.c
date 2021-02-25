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

void bst_find_smallest(loc x, loc retv) {
  loc unused2 = READ_LOC(retv, 0);
  if ((x == NULL)) {
    WRITE_INT(retv, 0, 7);
    return;
  }
  else {
    int vx2 = READ_INT(x, 0);
    loc lx2 = READ_LOC(x, 1);
    loc rx2 = READ_LOC(x, 2);
    bst_find_smallest(lx2, retv);
    int lo1x2 = READ_INT(retv, 0);
    WRITE_INT(retv, 0, ((vx2 <= lo1x2) ? vx2 : lo1x2));
    return;
  }
}
