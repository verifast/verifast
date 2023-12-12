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

/*
Copy in return statement is not elided.
*/
Foo copy_foo(const Foo &f) 
//@ requires copies |-> ? c &*& f.i |-> ?i;
//@ ensures copies |-> c + 1 &*& f.i |-> i &*& struct_Foo_padding(&result) &*& result.i |-> i;
{
    return f;
}


int main()
//@ requires module(copy_param, true);
//@ ensures true;
{
    //@ open_module();
    Foo f;
    Foo f_copy = copy_foo(f);
    //@ assert copies |-> 1;
    //@ leak copies |-> _;
}