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
