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

void bst_right_rotate(loc x, loc retv) {
  loc unused2 = READ_LOC(retv, 0);
  int v2 = READ_INT(x, 0);
  loc l2 = READ_LOC(x, 1);
  loc r2 = READ_LOC(x, 2);
  if ((l2 == NULL)) {
    return;

  }
  else {
    int vl22 = READ_INT(l2, 0);
    loc ll22 = READ_LOC(l2, 1);
    loc rl22 = READ_LOC(l2, 2);
    WRITE_LOC(l2, 2, x);
    WRITE_LOC(retv, 0, l2);
    WRITE_LOC(x, 1, rl22);
    return;
  }
}
