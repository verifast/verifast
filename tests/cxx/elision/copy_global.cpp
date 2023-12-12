static int copies = 0;

struct Foo {
    int i;

    Foo() : i(0) 
    //@ requires true;
    //@ ensures this->i |-> 0;
    {}

    Foo(const Foo &f) : i(f.i) 
    //@ requires copies |-> ?c &*& f.i |-> ?i;
    //@ ensures copies |-> c + 1 &*& f.i |-> i &*& this->i |-> i;
    {
        ++copies;
    }

    ~Foo()
    //@ requires this->i |-> _;
    //@ ensures true;
    {}
};

static Foo global_foo;

/*
Copy in return statement is not elided.
*/
Foo copy_foo() 
//@ requires copies |-> ?c &*& global_foo.i |-> ?i;
//@ ensures copies |-> c + 1 &*& global_foo.i |-> i &*& struct_Foo_padding(&result) &*& result.i |-> i;
{
    return global_foo;
}


int main()
//@ requires module(copy_global, true);
//@ ensures true;
{
    //@ open_module();
    Foo f = copy_foo();
    //@ assert copies |-> 1;
    //@ leak copies |-> _ &*& struct_Foo_padding(&global_foo) &*& global_foo.i |-> _;
}