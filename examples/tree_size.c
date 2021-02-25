
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

void tree_size(loc x, loc r) {
  if((x == 0)) {
    return;
  } else {
    loc l = READ_LOC(x, 1);
    loc rx = READ_LOC(x, 2);
    tree_size(l, r);
    int n1 = READ_INT(r, 0);
    WRITE_INT(r, 0, 0);
    tree_size(rx, r);
    int n = READ_INT(r, 0);
    WRITE_INT(r, 0, ((1 + n1) + n));
    return;
  }
}
