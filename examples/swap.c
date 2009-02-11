#include "stdlib.h"
#include "bool.h"

void swap(int *a, int *b)
    //@ requires integer(a, ?x) &*& integer(b, ?y);
    //@ ensures integer(a, y) &*& integer(b, x);
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

struct point {
    int x;
    int y;
};

void point_mirror(struct point *p)
    //@ requires p->x |-> ?x &*& p->y |-> ?y;
    //@ ensures p->x |-> y &*& p->y |-> x;
{
    //@ open point_x(p, x);
    //@ open point_y(p, y);
    swap(&p->x, &p->y);
    //@ close point_x(p, y);
    //@ close point_y(p, x);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct point *p = malloc(sizeof(struct point));
    if (p == 0) { abort(); }
    p->x = 3;
    p->y = 10;
    point_mirror(p);
    bool b = p->x == 10 && p->y == 3;
    assert(b);
    free(p);
    return 0;
}
