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
        copies += 1;
    }

    ~Foo()
    //@ requires this->i |-> _;
    //@ ensures true;
    {}
};

/*
Copy constructor of Foo has side-effect.
Eliding the copy in the return statement gives a different result from
performing the copy. Verification fails.
*/
Foo mk_foo() 
//@ requires copies |-> ?c;
/*@ ensures 
	copies |-> c + 1 &*& //~ copy constructor has side-effects, which does not occur when the copy is elided.
	struct_Foo_padding(&result) &*& 
	result.i |-> 10; 
@*/
{
    Foo f;
    f.i = 10;
    return f;
}


int main()
//@ requires module(copy_ctor_side_effect, true);
//@ ensures true;
{
    //@ open_module();
    Foo f = mk_foo();
    //@ assert f.i == 10;
    //@ leak copies |-> _;
}