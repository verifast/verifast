// Companion to struct_array_slice_wildcard.c, requires (produce) path.
struct Point { int x; int y; };

void use_points(struct Point *p, int n)
    //@ requires p[..n] |-> _;
    //@ ensures true;
{
}
