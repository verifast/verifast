struct Empty {

    Empty()
    //@ requires true;
    //@ ensures true;
    {}

    ~Empty()
    //@ requires true;
    //@ ensures true;
    {}
};

struct IntContainer {
    int i;

    IntContainer(int i) : i(i)
    //@ requires true;
    //@ ensures this->i |-> i;
    {}

    ~IntContainer()
    //@ requires this->i |-> _;
    //@ ensures true;
    {}
};

/*@
predicate IntPtrPred(IntPtr *iptr, int i) =
    iptr->i |-> ?ptr &*& new_block_ints(ptr, 1) &*& integer(ptr, i);
@*/

struct IntPtr {
    int *i;

    IntPtr(int i) : i(new int(i))
    //@ requires true;
    //@ ensures IntPtrPred(this, i);
    {
        //@ close IntPtrPred(this, i);
    }

    ~IntPtr()
    //@ requires IntPtrPred(this, _);
    //@ ensures true;
    {
        //@ open IntPtrPred(this, _);
        delete i;
    }
};

/*@
predicate NestedPred(Nested *nested, int j, int i) =
    nested->j |-> j &*&
    struct_IntPtr_padding(?iptr) &*&
    iptr == &nested->iptr &*&
    IntPtrPred(iptr, i);
@*/

struct Nested {
    int j;
    IntPtr iptr;

    Nested() : j(0), iptr(0)
    //@ requires true;
    //@ ensures NestedPred(this, 0, 0);
    {
        //@ close NestedPred(this, 0, 0);
    }

    ~Nested()
    //@ requires NestedPred(this, _, _);
    //@ ensures true;
    {
        //@ open NestedPred(this, _, _);
    }
};

int main()
//@ requires true;
//@ ensures true;
{
    Empty *empty = new Empty();
    IntContainer *ic = new IntContainer(1);
    Nested *n = new Nested();

    delete empty;
    delete ic;
    delete n;
}