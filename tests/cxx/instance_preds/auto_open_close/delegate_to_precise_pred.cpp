/*@
// Precise predicate which delegates to the instance predicate
predicate S_valid(S1 *s, std::type_info *t;) =
    s->valid(t)();
@*/

struct S1 {
    int x;

    /*@
    predicate valid() = this->x |-> ?x;
    @*/

    S1() : x(0)
    //@ requires true;
    //@ ensures S1_vtype(this, &typeid(S1)) &*& S_valid(this, &typeid(S1));
    {}

    virtual ~S1()
    //@ requires S1_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {}
};

struct S2 : public S1 {
    /*@
    predicate valid() = S2_bases_constructed(this) &*& this->valid(&typeid(S1))();
    @*/

    S2()
    //@ requires true;
    //@ ensures S2_vtype(this, &typeid(S2)) &*& valid();
    {}
    
    virtual ~S2()
    //@ requires S2_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {}
};

struct S3 : public S2 {
    /*@
    predicate valid() = S3_bases_constructed(this) &*& this->valid(&typeid(S2))();
    @*/

    S3()
    //@ requires true;
    //@ ensures S3_vtype(this, &typeid(S3)) &*& valid();
    {}
    
    ~S3()
    //@ requires S3_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {}
};

struct S4 : public S3 {
    /*@
    predicate valid() = 
        S4_bases_constructed(this) &*&
        S3_bases_constructed(this) &*&
        S2_bases_constructed(this) &*&
        S_valid(this, &typeid(S1));
    @*/
    
    S4()
    //@ requires true;
    //@ ensures S4_vtype(this, &typeid(S4)) &*& valid();
    {
        //@ open this->valid(&typeid(struct S3))();
        ++x;
    }
    
    ~S4()
    //@ requires S4_vtype(this, thisType) &*& valid();
    //@ ensures true;
    {}
};

int main()
//@ requires true;
//@ ensures true;
{
    S4 s4;
}