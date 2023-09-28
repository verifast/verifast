struct Foo {
    int x;
    //@ int y;

    Foo() : x(5)
    //@ requires true;
    //@ ensures this->x |-> 5 &*& this->y |-> 6;
    {
        //@ this->y = 6;
    }

    ~Foo()
    //@ requires this->x |-> _ &*& this->y |-> _;
    //@ ensures true;
    {}
};

int main()
//@ requires true;
//@ ensures true;
{
    Foo *f = new Foo;
    //@ assert f->x |-> 5 &*& f->y |-> 6;
    f->x = 0;
    //@ f->y = 1;
    //@ assert f->x |-> 0 &*& f->y |-> 1;
    delete f;
}