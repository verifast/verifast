typedef enum Foo { BAR, QUUX } Foo_t;
typedef enum { BAZ, ZAB } Quuz_t;

void test()
    //@ requires true;
    //@ ensures true;
{
    Foo_t x = BAR;
    //@ assert x == 0;
    enum Foo z = QUUX;
    //@ assert z == 1;
    Quuz_t y = BAZ;
    //@ assert y == 0;
}
