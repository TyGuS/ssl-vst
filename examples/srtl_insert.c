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

        

void srtl_insert(loc x, loc r) {
int k2 = READ_INT(r, 0);
if ((x == NULL)) {
loc y2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(r, 0, y2);
WRITE_LOC(y2, 1, NULL);
WRITE_INT(y2, 0, k2);
return;
}
else {
int vx2 = READ_INT(x, 0);
if (((k2 <= vx2) && (vx2 <= k2))) {
loc nxtx2 = READ_LOC(x, 1);
loc nxty2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(x, 1, nxty2);
WRITE_LOC(r, 0, x);
WRITE_LOC(nxty2, 1, nxtx2);
WRITE_INT(nxty2, 0, k2);
return;
} else {
if ((vx2 <= k2)) {
loc nxtx2 = READ_LOC(x, 1);
srtl_insert(nxtx2, r);
loc y12 = READ_LOC(r, 0);
WRITE_LOC(x, 1, y12);
WRITE_LOC(r, 0, x);
return;
} else {
loc nxtx2 = READ_LOC(x, 1);
loc nxty2 = (loc) malloc(2 * sizeof(loc));
WRITE_LOC(x, 1, nxty2);
WRITE_LOC(r, 0, x);
WRITE_LOC(nxty2, 1, nxtx2);
WRITE_INT(x, 0, k2);
WRITE_INT(nxty2, 0, vx2);
return;
}}}
}
