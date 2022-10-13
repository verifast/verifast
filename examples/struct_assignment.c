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
    
    t.p.x = 10;
    t.p.y = 20;
    t.q.x = 30;
    t.q.y = 40;

    //@ assert a.x == 1;
    //@ assert a.y == 2;

    a = b;
    //@ assert a.x == 3;
    //@ assert a.y == 4;
    r.p = r.q;
    //@ assert r.p.x == 7;
    //@ assert r.p.y == 8;
    r.q = t.p;
    //@ assert r.q.x == 10;
    //@ assert r.q.y == 20;
    a = r.p;
    //@ assert a.x == 7;
    //@ assert a.y == 8;
    t.p = b;
    //@ assert t.p.x |-> 3 &*& t.p.y |-> 4;
    
    r = t;
    //@ assert r.p.x == 3 && r.p.y == 4 && r.q.x == 30 && r.q.y == 40;
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

    r.q = a;
    //@ assert r.q.x |-> 1 &*& r.q.y |-> 2;
    t.p = b;
    //@ assert t.p.x |-> 3 &*& t.p.y |-> 4;
    a = b;
    //@ assert a.x |-> 3 &*& a.y |-> 4;
    r.p = r.q;
    //@ assert r.p.x |-> 1 &*& r.p.y |-> 2 &*& r.q.x |-> 1 &*& r.q.y |-> 2;
    r.q = t.p;
    //@ assert r.p.x |-> 1 &*& r.p.y |-> 2 &*& r.q.x |-> 3 &*& r.q.y |-> 4;
    a = r.p;
    //@ assert a.x |-> 1 &*& a.y |-> 2;
    t.q = b;
    //@ assert t.q.x |-> 3 &*& t.q.y |-> 4;
    
    r = t;
    //@ assert r.p.x |-> 3 &*& r.p.y |-> 4 &*& r.q.x |-> 3 &*& r.q.y |-> 4;
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