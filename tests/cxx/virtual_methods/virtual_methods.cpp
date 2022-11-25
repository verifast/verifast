class AVirtual
{
public:
  AVirtual()
  //@ requires true;
  //@ ensures AVirtual_vtype(this, &typeid(struct AVirtual));
  {
    foo();
  }
  
  virtual ~AVirtual() 
  //@ requires AVirtual_vtype(this, &typeid(struct AVirtual));
  //@ ensures true;
  {}
  
  virtual void foo() const
  //@ requires AVirtual_vtype(this, ?t);
  //@ ensures AVirtual_vtype(this, t);
  {}
};

class B
{
public:
  B()
  //@ requires true;
  //@ ensures true;
  {}

  ~B()
  //@ requires true;
  //@ ensures true;
  {}

  void foo(AVirtual &a) const 
  //@ requires &a != 0 &*& AVirtual_vtype(&a, ?t);
  //@ ensures AVirtual_vtype(&a, t);
  {
    a.foo();
  }
};

class CVirtual
{
public:
  CVirtual()
  //@ requires true;
  //@ ensures CVirtual_vtype(this, &typeid(struct CVirtual));
  {}

  virtual ~CVirtual()
  //@ requires CVirtual_vtype(this, &typeid(struct CVirtual));
  //@ ensures true;
  {}

  virtual void foo() const
  //@ requires CVirtual_vtype(this, ?t);
  //@ ensures CVirtual_vtype(this, t);
  {}

  void bar() const
  //@ requires CVirtual_vtype(this, ?t);
  //@ ensures CVirtual_vtype(this, t);
  {
    foo();
  }
};

class DVirtual : public AVirtual, public B, public CVirtual
{
public:
  DVirtual()
  //@ requires true;
  //@ ensures DVirtual_bases_constructed(this) &*& DVirtual_vtype(this, &typeid(struct DVirtual));
  {}

  ~DVirtual()
  //@ requires DVirtual_bases_constructed(this) &*& DVirtual_vtype(this, &typeid(struct DVirtual));
  //@ ensures true;
  {}

  void foo() const override
  //@ requires DVirtual_bases_constructed(this) &*& DVirtual_vtype(this, ?t);
  //@ ensures DVirtual_bases_constructed(this) &*& DVirtual_vtype(this, t);
  {}

};

void foo(AVirtual &a)
//@ requires &a != 0 &*& AVirtual_vtype(&a, ?t);
//@ ensures AVirtual_vtype(&a, t);
{
  a.foo();
}

int main()
//@ requires true;
//@ ensures true;
{
  DVirtual d;
  d.foo();
  AVirtual &aref = d;
  aref.foo();
  foo(aref);
  d.AVirtual::foo();
  d.bar();
  d.B::foo(aref);
}