struct A {
    //@ predicate valid() = true;
	
    A()
    //@ requires true;
    //@ ensures A_vtype(this, &typeid(A)) &*& valid();
    {
        //@ close valid();
    }

    virtual ~A()
    //@ requires A_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {
        //@ open valid();
    }

    virtual int foo(int i)
    //@ requires valid() &*& 0 < i && i < 100;
    //@ ensures valid() &*& result != 0;
    {
        return i;
    }
};

struct B : public A {
    //@ predicate valid() = B_bases_constructed(this) &*& this->valid(&typeid(A))();

    B()
    //@ requires true;
    //@ ensures B_vtype(this, &typeid(B)) &*& valid();
    {
        //@ close valid();
    }

    ~B()
    //@ requires B_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {
        //@ open valid();
    }

    int foo(int i)
    //@ requires valid() &*& i > 0;
    //@ ensures valid() &*& result > 100;
    {
        //@ open valid();
        return i + 100;
        //@ close valid();
    }
};

struct C : public B {
    //@ predicate valid() = C_bases_constructed(this) &*& this->valid(&typeid(B))();

    C()
    //@ requires true;
    //@ ensures C_vtype(this, &typeid(C)) &*& valid();
    {
        //@ close valid();
    }

    ~C()
    //@ requires C_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {
        //@ open valid();
    }

    int foo(int i)
    //@ requires valid();
    //@ ensures valid() &*& result == 200;
    {
        //@ open valid();
        return 200;
        //@ close valid();
    }
};