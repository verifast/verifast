struct Foo {
    int i;

    Foo() : i(0) 
    //@ requires true;
    //@ ensures this->i |-> 0;
    {}

    Foo(const Foo &f) : i(f.i) 
    //@ requires f.i |-> ?i;
    //@ ensures f.i |-> i &*& this->i |-> i;
    {}

    ~Foo()
    //@ requires this->i |-> _;
    //@ ensures true;
    {}
};

/*
Copy constructor of Foo has no side-effects.
Eliding the copy in the return statement gives the same result as
performing the copy.
*/
Foo mk_foo() 
//@ requires true;
//@ ensures struct_Foo_padding(&result) &*& result.i |-> 10;
{
    Foo f;
    f.i = 10;
    return f;
}


int main()
//@ requires true;
//@ ensures true;
{
    Foo f = mk_foo();
    //@ assert f.i == 10;
}