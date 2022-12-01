struct A
{
  A()
  //@ requires true;
  //@ ensures A_vtype(this, &typeid(A));
  {}
  
  ~A()
  //@ requires A_vtype(this, &typeid(A));
  //@ ensures true;
  {}
  
  virtual void foo() const
  //@ requires true;
  //@ ensures true;
  {}
};

void callVirtualMeth(A &a)
//@ requires &a != 0;
//@ ensures true;
{
  a.foo(); //~
}