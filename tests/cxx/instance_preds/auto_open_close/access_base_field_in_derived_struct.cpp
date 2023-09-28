struct Base {
    /*@
    predicate valid() = 
        this->x |-> ?x;
    @*/

    int x;

    Base() : x(0)
    //@ requires true;
    //@ ensures valid();
    {}

    ~Base()
    //@ requires valid();
    //@ ensures true;
    {}
};

struct Derived : public Base {
    /*@
    predicate valid() =
        Derived_bases_constructed(this) &*&
        this->valid(&typeid(Base))() &*&
        this->j |-> ?j;
    @*/

    int j;

    Derived() : j(0)
    //@ requires true;
    //@ ensures valid();
    {}

    ~Derived()
    //@ requires valid();
    //@ ensures true;
    {}

    void incrX()
    //@ requires valid();
    //@ ensures valid();
    {
        ++x;
    }

    void incrJ()
    //@ requires valid();
    //@ ensures valid();
    {
        ++j;
    }
};

int main()
//@ requires true;
//@ ensures true;
{
    Derived d;
    d.incrX();
    d.incrJ();
}