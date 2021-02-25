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

        

void mk_acc(loc r, int id) {
int bal2 = READ_INT(r, 0);
loc x2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(r, 0, x2);
WRITE_INT(x2, 0, id);
WRITE_INT(x2, 1, bal2);
return;

}
