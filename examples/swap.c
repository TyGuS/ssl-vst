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

        

void swap(loc x, loc y) {
loc a2 = READ_LOC(x, 0);
loc b2 = READ_LOC(y, 0);
WRITE_LOC(x, 0, b2);
WRITE_LOC(y, 0, a2);
return;

}
