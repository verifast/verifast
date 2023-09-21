struct First {
    int f;

    /*@
    predicate valid() = this->f |-> ?f;
    @*/

    First() : f(0)
    //@ requires true;
    //@ ensures valid();
    {}

    ~First()
    //@ requires valid();
    //@ ensures true;
    {}
};

struct Second {
    First f;

    /*@
    predicate valid() = struct_First_padding(&this->f) &*& this->f.valid();
    @*/

    Second()
    //@ requires true;
    //@ ensures valid();
    {}

    ~Second()
    //@ requires valid();
    //@ ensures true;
    {}
    
    void incrFirst()
    //@ requires valid();
    //@ ensures valid();
    {
        ++f.f;
    }
};

struct Bar {
    int s;

    /*@
    predicate valid() = this->s |-> ?s;
    @*/

    Bar() : s(0)
    //@ requires true;
    //@ ensures Bar_vtype(this, &typeid(Bar)) &*& valid();
    {}

    virtual ~Bar()
    //@ requires Bar_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {}
};

struct Foo : public Bar {
    /*@
    predicate valid() = Foo_bases_constructed(this) &*& this->valid(&typeid(Bar))();
    @*/

    Foo()
    //@ requires true;
    //@ ensures Foo_vtype(this, &typeid(Foo)) &*& valid();
    {}

    ~Foo()
    //@ requires Foo_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {}
};

void incr(Foo &f)
//@ requires f.valid(&typeid(Foo))();
//@ ensures f.valid(&typeid(Foo))();
{
    ++f.s;
}

int main()
//@ requires true;
//@ ensures true;
{
    Second s;
    Foo f;

    incr(f);
}