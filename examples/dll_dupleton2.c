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

void dll_dupleton(int x, int y, loc r) {
  loc a = READ_LOC(r, 0);
  loc z = (loc) malloc(3 * sizeof(loc));
  loc w = (loc) malloc(3 * sizeof(loc));
  WRITE_LOC(r, 0, z);
  WRITE_LOC(z, 1, w);
  WRITE_LOC(z, 2, 0);
  WRITE_LOC(w, 1, 0);
  WRITE_LOC(w, 2, z);
  WRITE_INT(z, 0, x);
  WRITE_INT(w, 0, y);
  return;
}
