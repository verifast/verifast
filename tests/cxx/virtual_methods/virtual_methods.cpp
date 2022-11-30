class A
{
  int m_i;

public:
  A() : m_i(0)
  //@ requires true;
  //@ ensures A_vtype(this, &typeid(A)) &*& this->m_i |-> 0;
  {}
  
  virtual ~A()
  //@ requires A_vtype(this, &typeid(A)) &*& this->m_i |-> _;
  //@ ensures true;
  {}
  
  int getI() const
  //@ requires this->m_i |-> ?i;
  //@ ensures this->m_i |-> i &*& result == i;
  {
    return m_i;
  }
  
  virtual int getVirtualI() const
  //@ requires this->m_i |-> ?i;
  //@ ensures this->m_i |-> i &*& result == i;
  {
    return getI();
  }
  
  void callVirtualMeth() const
  //@ requires A_vtype(this, ?t) &*& this->m_i |-> ?i;
  //@ ensures A_vtype(this, t) &*& this->m_i |-> i;
  {
    getVirtualI();
  }
  
  virtual void virtualCallVirtualMeth() const
  //@ requires A_vtype(this, ?t) &*& this->m_i |-> ?i;
  //@ ensures A_vtype(this, t) &*& this->m_i |-> i;
  {
    getVirtualI();
  }
};

class B : public A
{
public:
  B()
  //@ requires true;
  /*@ ensures 
      B_bases_constructed(this) &*& 
      B_vtype(this, &typeid(B)) &*& 
      A_m_i(this, 0);
  @*/
  {}
  
  virtual ~B()
  /*@ requires 
      B_bases_constructed(this) &*& 
      B_vtype(this, &typeid(B)) &*& 
      A_m_i(this, _);
  @*/
  //@ ensures true;
  {}
  
  void callVirtualFromBase() const
  /*@ requires 
      B_bases_constructed(this) &*& 
      A_vtype(this, ?t) &*& 
      A_m_i(this, ?i);
  @*/
  /*@ ensures 
      B_bases_constructed(this) &*&
      A_vtype(this, t) &*& 
      A_m_i(this, i);
  @*/
  {
    callVirtualMeth();
  }
  
  void callStaticallyBoundCall() const
  /*@ requires
      B_bases_constructed(this) &*&
      A_m_i(this, ?i);
  @*/
  /*@ ensures
      B_bases_constructed(this) &*&
      A_m_i(this, i);
  @*/
  {
    A::getVirtualI();
  }
};

int main()
//@ requires true;
//@ ensures true;
{
  A a;
  a.getI();
  a.getVirtualI();
  a.callVirtualMeth();
  a.virtualCallVirtualMeth();
  B b;
  b.getVirtualI();
  b.A::getVirtualI();
  b.callVirtualMeth();
  b.virtualCallVirtualMeth();
  b.callVirtualFromBase();
  b.callStaticallyBoundCall();
  A &aref = b;
  aref.getI();
  aref.getVirtualI();
  aref.callVirtualMeth();
  aref.virtualCallVirtualMeth();
}