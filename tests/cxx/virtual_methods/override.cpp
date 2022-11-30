class A 
{
  int m_i;
public:
  A() : m_i(0)
  //@ requires true;
  //@ ensures this->m_i |-> 0;
  {}

  ~A()
  //@ requires this->m_i |-> _;
  //@ ensures true;
  {}
};

class B
{
  int m_i;
public:
  B() : m_i(0)
  //@ requires true;
  /*@ ensures 
      B_vtype(this, &typeid(B)) &*&
      this->m_i |-> 0;
  @*/
  {}

  ~B()
  /*@ requires 
      B_vtype(this, &typeid(B)) &*&
      this->m_i |-> _;
  @*/
  //@ ensures true;
  {}

  int getI() const
  //@ requires this->m_i |-> ?i;
  //@ ensures this->m_i |-> i;
  {
    return m_i;
  }
  
  virtual int someInt() const
  /*@ requires 
      this->m_i |-> ?i &*&
      exists<struct C*>(?thisC) &*& 
      this == thisC &*& 
      C_bases_constructed(thisC);
  @*/
  /*@ ensures
      this->m_i |-> i &*&
      C_bases_constructed(thisC);
  @*/
  {
    return getI();
  }
};

class C : public A, public B
{
public:
  C()
  //@ requires true;
  /*@ ensures
      C_bases_constructed(this) &*&
      A_m_i(this, 0) &*&
      B_m_i(this, 0) &*&
      C_vtype(this, &typeid(C));
  @*/
  {}

  ~C()
  /*@ requires
      C_bases_constructed(this) &*&
      A_m_i(this, _) &*&
      B_m_i(this, _) &*&
      C_vtype(this, &typeid(C));
  @*/
  //@ ensures true;
  {}
  
  virtual int someInt() const override
  /*@ requires 
      B_m_i(this, ?i) &*&
      C_bases_constructed(this);
  @*/
  /*@ ensures
      B_m_i(this, i) &*&
      C_bases_constructed(this);
  @*/
  {
    int result = getI();
    return result * 5;
  }
};

int main()
//@ requires true;
//@ ensures true;
{
  C c;
  c.someInt();
}
