#include "malloc.h"
#include "stdlib.h"

struct point {
    int x;
    int y;
};

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ chars_split((void *)points, sizeof(struct point));
    //@ close_struct(points);
    //@ close_struct(points + 1);
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    //@ open_struct(points);
    //@ open_struct(points + 1);
    //@ chars_join((void *)points);
    free((void *)points); 
    return 0;
}