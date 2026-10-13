// Struct-typed array slice with `_` pattern used to crash with Not_found.
struct Point { int x; int y; };

struct Point *alloc_points(int n)
    //@ requires n >= 0;
    //@ ensures result[..n] |-> _;
{
  return 0;
}
