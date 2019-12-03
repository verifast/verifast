struct foo {
    int x;
    int y;
};

struct bar {
    struct foo p;
    struct foo q;
};

void test()
//@ requires true;
//@ ensures true;
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};
    
    struct bar r;
    struct bar t;

    a = b;
    r.p = r.q;
    r.q = t.p;
    a = r.p;
    t.p = b;
    
    r = t;
}