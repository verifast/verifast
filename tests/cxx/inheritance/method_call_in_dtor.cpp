struct A
{
    A()
    //@ requires true;
    //@ ensures true;
    {}

    ~A()
    //@ requires true;
    //@ ensures true;
    {}
};

class B : public A
{
    int *m_i;
    
    void cleanup()
    /*@ requires 
        [?f]B_bases_constructed(this) &*& 
        this->m_i |-> ?i_addr &*&
        integer(i_addr, _) &*&
        new_block_ints(i_addr, 1);
    @*/
    /*@ ensures
        [f]B_bases_constructed(this) &*&
        this->m_i |-> i_addr;
    @*/
    {
        delete m_i;
    }
public:
    B()
    //@ requires true;
    /*@ ensures 
        B_bases_constructed(this) &*& 
        this->m_i |-> ?i_addr &*&
        integer(i_addr, 0) &*&
        new_block_ints(i_addr, 1);
    @*/
    {
        m_i = new int(0);
    }
    
    ~B()
    /*@ requires
        B_bases_constructed(this) &*&
        this->m_i |-> ?i_addr &*&
        integer(i_addr, _) &*&
        new_block_ints(i_addr, 1);
    @*/
    //@ ensures true;
    {
        cleanup();
    }
    
};
