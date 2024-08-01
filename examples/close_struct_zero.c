#include <stdlib.h>
#include <string.h>

typedef struct Point {
    int x;
    int y;
} Point;

int main(void)
    //@ requires true;
    //@ ensures  true;
{
    //@ assume(sizeof(Point) < UINT_MAX);
    Point *p = malloc(sizeof(Point) + 0);
    if (p == 0) abort();
    //@ assume(has_type(p, &typeid(struct Point)));

    memset(p, 0, sizeof(Point));
    //@ close_struct_zero(p);

    //@ assert p->x |-> 0 &*& p->y |-> 0 &*& struct_Point_padding(p);

    //@ open_struct(p);
    free((void *)p);

    return 0;
}