class A
{
  int m_i;

public:
  /*@
  predicate valid(int i) =
    this->m_i |-> i;
  @*/
  
  A() : m_i(0)
  //@ requires true;
  //@ ensures A_vtype(this, thisType) &*& valid(0);
  {
    //@ close valid(0);
  }
  
  virtual ~A()
  //@ requires A_vtype(this, thisType) &*& valid(_);
  //@ ensures true;
  {
    //@ open valid(_);
  }

  virtual A & operator=(A const &) = delete;
  
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
  /*@
  predicate valid(int i) =
    this->valid(&typeid(A))(i) &*&
    B_bases_constructed(this);
  @*/

  B()
  //@ requires true;
  /*@ ensures 
      valid(0) &*&
      B_vtype(this, thisType);
  @*/
  {
    //@ close valid(0);
  }
  
  virtual ~B()
  /*@ requires 
      valid(_) &*&
      B_vtype(this, thisType);
  @*/
  //@ ensures true;
  {
    //@ open valid(_);
  }
  
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
  
  virtual void pure() = 0;
  //@ requires true;
  //@ ensures true;
};

void test(B &b)
//@ requires &b != 0 &*& B_vtype(&b, &typeid(B)) &*& b.valid(&typeid(B))(?i);
//@ ensures B_vtype(&b, &typeid(B)) &*& b.valid(&typeid(B))(i);
{
  A a;
  //@ open a.valid(0);
  a.getI();
  a.getVirtualI();
  a.callVirtualMeth();
  a.virtualCallVirtualMeth();
  //@ open b.valid(i);
  //@ open b.valid(&typeid(struct A))(_);
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
  //@ close b.valid(&typeid(struct A))(_);
  //@ close b.valid(_);
  //@ close a.valid(_);
}