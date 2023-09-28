/*
Check that a derived class can refer to an instance predicate in a base class, which the derived class did not override.
*/

struct Bar {
    int x;

    /*@
    predicate Bar_valid() = this->x |-> ?x;
    @*/

    Bar() : x(0)
    //@ requires true;
    //@ ensures Bar_valid();
    {}

    ~Bar()
    //@ requires Bar_valid();
    //@ ensures true;
    {}
};

struct Foo : public Bar {
    int y;

    /*@
    predicate Foo_valid() = Foo_bases_constructed(this) &*& this->Bar_valid(&typeid(Bar))() &*& this->y |-> ?y;
    @*/

    Foo() : y(0)
    //@ requires true;
    //@ ensures Foo_valid();
    {}

    ~Foo()
    //@ requires Foo_valid();
    //@ ensures true;
    {}
};

struct S1 {
    int x;

    /*@
    predicate S_valid() = this->x |-> ?x;
    @*/

    S1() : x(0)
    //@ requires true;
    //@ ensures S_valid();
    {}

    ~S1()
    //@ requires S_valid();
    //@ ensures true;
    {}
};

struct S2 : public S1 {
    /*@
    predicate valid() = S2_bases_constructed(this) &*& this->S_valid(&typeid(S1))();
    @*/

    S2()
    //@ requires true;
    //@ ensures valid();
    {}
    
    ~S2()
    //@ requires valid();
    //@ ensures true;
    {}
};

struct S3 : public S2 {
    /*@
    predicate valid() = S3_bases_constructed(this) &*& this->valid(&typeid(S2))();
    @*/

    S3()
    //@ requires true;
    //@ ensures valid();
    {}
    
    ~S3()
    //@ requires valid();
    //@ ensures true;
    {}
};

struct S4 : public S3 {
    /*@
    predicate valid() = 
        S4_bases_constructed(this) &*&
        S3_bases_constructed(this) &*&
        S2_bases_constructed(this) &*&
        this->S_valid(&typeid(S1))();
    @*/
    
    S4()
    //@ requires true;
    //@ ensures valid();
    {
        ++x;
    }
    
    ~S4()
    //@ requires valid();
    //@ ensures true;
    {}
};

int main()
//@ requires true;
//@ ensures true;
{
    Bar b;
    S4 s4;
}