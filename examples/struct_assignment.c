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
    
    struct bar r = {{5, 6}, {7, 8}};
    struct bar t;

    //@ assert a.x == 1;
    //@ assert a.y == 2;

    a = b;
    //@ assert a.x == 3;
    //@ assert a.y == 4;
    r.p = r.q;
    //@ assert r.p.x == 7;
    //@ assert r.p.y == 8;
    r.q = t.p;
    a = r.p;
    t.p = b;
    
    r = t;
}

void test2()
//@ requires true;
//@ ensures true;
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};
    
    struct bar r;
    struct bar t;
    
    //@ { &a; &b; &r; &t; }

    a = b;
    r.p = r.q;
    r.q = t.p;
    a = r.p;
    t.p = b;
    
    r = t;
}

void test3()
//@ requires true;
//@ ensures true;
{
    struct foo a = {1, 2};
    struct foo b = {3, 4};
    
    struct bar r;
    struct bar t;
    
    //@ { &a; &t; }

    a = b;
    r.p = r.q;
    r.q = t.p;
    a = r.p;
    t.p = b;
    
    r = t;
}