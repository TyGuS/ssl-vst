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

        

void sll_singleton(int x, loc p) {
loc a2 = READ_LOC(p, 0);
loc y2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(p, 0, y2);
WRITE_LOC(y2, 1, NULL);
WRITE_INT(y2, 0, x);
return;

}
