#define INT_MAX 2147483647

/* ========================================================================== */
/* Positive Verified C++ Classes & Methods                                    */
/* ========================================================================== */

struct Shape {
    //@ predicate valid() = true;

    Shape()
    //@ requires true;
    //@ ensures Shape_vtype(this, thisType) &*& valid();
    {
        //@ close valid();
    }

    virtual ~Shape()
    //@ requires Shape_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {
        //@ open valid();
    }

    virtual int area(int scale)
    //@ requires valid() &*& 0 <= scale && scale < 1000;
    //@ ensures valid() &*& result >= 0;
    {
        return scale;
    }
};

struct Box : public Shape {
    int width;
    int height;

    //@ predicate valid() = this->valid(&typeid(Shape))() &*& Box_bases_constructed(this) &*& this->width |-> ?w &*& this->height |-> ?h &*& 0 <= w && w < 100 &*& 0 <= h && h < 100;

    Box(int w, int h) : width(w), height(h)
    //@ requires 0 <= w && w < 100 &*& 0 <= h && h < 100;
    //@ ensures Box_vtype(this, thisType) &*& valid();
    {
        //@ close valid();
    }

    virtual ~Box()
    //@ requires Box_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {
        //@ open valid();
    }

    virtual int area(int scale) override
    //@ requires valid() &*& 0 <= scale && scale < 1000;
    //@ ensures valid() &*& result >= 0;
    {
        //@ open valid();
        int res = width + height + scale;
        //@ close valid();
        return res;
    }
};

void safe_cxx_stack_and_ref()
//@ requires true;
//@ ensures true;
{
    int x = 42;
    int &ref = x;
    ref = 99;
    //@ assert x == 99;
}

void safe_cxx_polymorphic_delete()
//@ requires true;
//@ ensures true;
{
    Box *b = new Box(10, 20);
    Shape *s = b;
    //@ upcast_new_block((struct Shape *)b);
    delete s;
}

/* ========================================================================== */
/* Negative Soundness Tests (12 Should-Fail Cases)                            */
/* ========================================================================== */

/* 1. Deleting a derived class via base pointer without a virtual destructor */
struct NonVirtBase {
    //@ predicate valid() = true;
    NonVirtBase()
    //@ requires true;
    //@ ensures valid();
    {
        //@ close valid();
    }
    ~NonVirtBase()
    //@ requires valid();
    //@ ensures true;
    {
        //@ open valid();
    }
};

struct DerivedNV : public NonVirtBase {
    /*@ predicate valid() =
        this->valid(&typeid(NonVirtBase))() &*& DerivedNV_bases_constructed(this);
    @*/
    DerivedNV()
    //@ requires true;
    //@ ensures valid() &*& DerivedNV_vtype(this, thisType);
    {
        //@ close valid();
    }
    virtual ~DerivedNV()
    //@ requires valid() &*& DerivedNV_vtype(this, thisType);
    //@ ensures true;
    {
        //@ open valid();
    }
};

void neg_delete_nonvirtual_base()
//@ requires true;
//@ ensures true;
{
    DerivedNV *d = new DerivedNV;
    //@ open d->valid();
    //@ upcast_new_block((struct NonVirtBase *)d); //~ should_fail
    delete d; //~allow_dead_code
}

/* 2. Binding an lvalue reference to dereferenced nullptr */
void neg_null_reference_bind()
//@ requires true;
//@ ensures true;
{
    int *p = 0;
    int &ref = *p; //~ should_fail
}

/* 3. Passing dereferenced nullptr to reference parameter */
void takes_int_ref(int &r)
//@ requires true;
//@ ensures true;
{
}

void neg_pass_null_to_reference_param()
//@ requires true;
//@ ensures true;
{
    int *p = 0;
    takes_int_ref(*p); //~ should_fail
}

/* 4. Derived virtual method overriding base method postcondition violation */
struct BrokenShape : public Shape {
    //@ predicate valid() = this->valid(&typeid(Shape))() &*& BrokenShape_bases_constructed(this);

    BrokenShape()
    //@ requires true;
    //@ ensures BrokenShape_vtype(this, thisType) &*& valid();
    {
        //@ close valid();
    }

    virtual ~BrokenShape()
    //@ requires BrokenShape_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {
        //@ open valid();
    }

    virtual int area(int scale) override
    //@ requires valid() &*& 0 <= scale && scale < 1000;
    //@ ensures valid() &*& result >= 0; //~ should_fail
    {
        return -1;
    }
};

/* 5. Calling virtual method with violated precondition */
void neg_virtual_method_precond_violation(Shape *s)
//@ requires s != 0 &*& Shape_vtype(s, ?t) &*& s->valid(t)();
//@ ensures Shape_vtype(s, t) &*& s->valid(t)();
{
    s->area(-10); //~ should_fail
}

/* 6. Accessing member field in constructor before initialization */
struct UninitFieldCtor {
    int a;
    int b;

    UninitFieldCtor()
    //@ requires true;
    //@ ensures this->a |-> 1 &*& this->b |-> 2;
    {
        int x = this->a; //~ should_fail
        this->a = 1; //~allow_dead_code
        this->b = 2; //~allow_dead_code
    }
};

/* 7. Use-after-delete on a C++ object */
struct SimpleObj {
    int val;

    SimpleObj() : val(0)
    //@ requires true;
    //@ ensures this->val |-> 0;
    {}

    ~SimpleObj()
    //@ requires this->val |-> _;
    //@ ensures true;
    {}

    void setVal(int v)
    //@ requires this->val |-> _;
    //@ ensures this->val |-> v;
    {
        val = v;
    }
};

void neg_use_after_delete()
//@ requires true;
//@ ensures true;
{
    SimpleObj *s = new SimpleObj();
    delete s;
    s->setVal(42); //~ should_fail
}

/* 8. Calling member method through nullptr */
void neg_null_object_method_call()
//@ requires true;
//@ ensures true;
{
    SimpleObj *s = 0;
    s->setVal(42); //~ should_fail
}

/* 9. Typeid equality assertion failure on distinct types */
void neg_typeid_equality_mismatch()
//@ requires true;
//@ ensures true;
{
    //@ assert &typeid(int) == &typeid(float); //~ should_fail
}

/* 10. Arithmetic overflow in C++ method */
int neg_cxx_arithmetic_overflow(int x)
//@ requires x == INT_MAX;
//@ ensures true;
{
    return x + 1; //~ should_fail
}

/* 11. Division by zero in C++ method */
int neg_cxx_div_zero(int x)
//@ requires true;
//@ ensures true;
{
    return x / 0; //~ should_fail
}

/* 12. Memory leak in C++ function */
void neg_cxx_memory_leak()
//@ requires true;
//@ ensures emp;
{
    SimpleObj *s = new SimpleObj();
} //~ should_fail
