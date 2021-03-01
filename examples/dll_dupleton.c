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
loc a2 = READ_LOC(r, 0);
loc z2 = (loc) malloc(3 * sizeof(loc));
loc wz2 = (loc) malloc(3 * sizeof(loc));
WRITE_LOC(r, 0, z2);
WRITE_LOC(z2, 1, wz2);
WRITE_LOC(z2, 2, NULL);
WRITE_LOC(wz2, 1, NULL);
WRITE_LOC(wz2, 2, z2);
WRITE_INT(z2, 0, x);
WRITE_INT(wz2, 0, y);
return;

}
