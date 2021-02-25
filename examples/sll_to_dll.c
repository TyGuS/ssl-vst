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

        

void sll_to_dll(loc f) {
loc x2 = READ_LOC(f, 0);
if ((x2 == NULL)) {
return;
}
else {
int vx22 = READ_INT(x2, 0);
loc nxtx22 = READ_LOC(x2, 1);
WRITE_LOC(f, 0, nxtx22);
sll_to_dll(f);
loc i12 = READ_LOC(f, 0);
if ((i12 == NULL)) {
loc i2 = (loc) malloc(3 * sizeof(loc));
free(x2);
WRITE_LOC(f, 0, i2);
WRITE_LOC(i2, 1, NULL);
WRITE_LOC(i2, 2, NULL);
WRITE_INT(i2, 0, vx22);
return;
}
else {
int vi122 = READ_INT(i12, 0);
loc wi122 = READ_LOC(i12, 1);
loc i2 = (loc) malloc(3 * sizeof(loc));
free(x2);
WRITE_LOC(i12, 2, i2);
WRITE_LOC(f, 0, i2);
WRITE_LOC(i2, 1, i12);
WRITE_LOC(i2, 2, NULL);
WRITE_INT(i12, 0, vx22);
WRITE_INT(i2, 0, vi122);
return;
}}
}
