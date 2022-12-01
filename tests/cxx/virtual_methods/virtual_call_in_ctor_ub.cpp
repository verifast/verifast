struct AVirtual
{
  int m_a;

  AVirtual(AVirtual *a) : m_a(0)
  //@ requires true;
  //@ ensures AVirtual_vtype(this, &typeid(struct AVirtual)) &*& this->m_a |-> 0;
  {
    foo();
  }

  virtual ~AVirtual()
  //@ requires AVirtual_vtype(this, &typeid(struct AVirtual)) &*& this->m_a |-> _;
  //@ ensures true;
  {
    foo();
  }

  int getI() const
  //@ requires this->m_a |-> ?a;
  //@ ensures this->m_a |-> a &*& result == a;
  {
    return m_a;
  }

  virtual void foo() const
  //@ requires AVirtual_vtype(this, ?t);
  //@ ensures AVirtual_vtype(this, t);
  {}
};

struct BVirtual
{
  int m_b;

  BVirtual(AVirtual *av) : m_b(av->m_a)
  //@ requires av != 0 &*& av->m_a |-> ?a;
  //@ ensures av->m_a |-> a &*& BVirtual_vtype(this, &typeid(struct BVirtual)) &*& this->m_b |-> a;
  {
    av->foo(); //~
  }

  virtual ~BVirtual()
  //@ requires BVirtual_vtype(this, &typeid(struct BVirtual)) &*& this->m_b |-> _;
  //@ ensures true;
  {}

  virtual void bar() const
  //@ requires BVirtual_vtype(this, ?t);
  //@ ensures BVirtual_vtype(this, t);
  {}
};

struct CVirtual : AVirtual, BVirtual
{
  CVirtual() : AVirtual(this), BVirtual(this)
  //@ requires true;
  /*@ ensures 
      CVirtual_bases_constructed(this) &*& 
      CVirtual_vtype(this, &typeid(struct CVirtual)) &*&
      AVirtual_m_a(this, 0) &*&
      BVirtual_m_b(this, 0);
  @*/
  {
    foo();
  }

  ~CVirtual()
  /*@ requires 
      CVirtual_bases_constructed(this) &*& 
      CVirtual_vtype(this, &typeid(struct CVirtual)) &*&
      AVirtual_m_a(this, _) &*&
      BVirtual_m_b(this, _);
  @*/
  //@ ensures true;
  {
    bar();
    foo();
  }
};

int main()
//@ requires true;
//@ ensures true;
{
  CVirtual c;
  c.foo();
  c.bar();
  int a = c.getI();
  //@ assert a == 0;
}