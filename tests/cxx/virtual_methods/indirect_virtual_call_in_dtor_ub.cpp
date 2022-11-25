struct BVirtual;

struct AVirtual
{
  int m_a;
  BVirtual *m_bv;

  AVirtual(AVirtual *a, BVirtual *b) : m_a(0), m_bv(b)
  //@ requires true;
  /*@ ensures 
      AVirtual_vtype(this, &typeid(struct AVirtual)) &*& 
      this->m_a |-> 0 &*&
      this->m_bv |-> b;
  @*/
  {
    foo();
  }

  virtual ~AVirtual();
  /*@ requires 
      AVirtual_vtype(this, &typeid(struct AVirtual)) &*& 
      this->m_a |-> _ &*&
      this->m_bv |-> ?bv &*&
      bv != 0;
  @*/
  //@ ensures true;

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
  /*@ ensures 
      av->m_a |-> a &*& 
      BVirtual_vtype(this, &typeid(struct BVirtual)) &*& 
      this->m_b |-> a;
  @*/
  {}

  virtual ~BVirtual()
  /*@ requires 
      BVirtual_vtype(this, &typeid(struct BVirtual)) &*& 
      this->m_b |-> _;
  @*/
  //@ ensures true;
  {}

  virtual void bar() const
  //@ requires BVirtual_vtype(this, ?t);
  //@ ensures BVirtual_vtype(this, t);
  {}
};

struct CVirtual : AVirtual, BVirtual
{
  CVirtual() : AVirtual(this, this), BVirtual(this)
  //@ requires true;
  /*@ ensures 
      CVirtual_bases_constructed(this) &*& 
      CVirtual_vtype(this, &typeid(struct CVirtual)) &*&
      AVirtual_m_a(this, 0) &*&
      AVirtual_m_bv(this, this) &*&
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
      AVirtual_m_bv(this, this) &*&
      BVirtual_m_b(this, _);
  @*/
  //@ ensures true;
  {
    bar();
    foo();
  }
};

void bar(BVirtual *bv)
//@ requires bv != 0 &*& BVirtual_vtype(bv, ?t);
//@ ensures BVirtual_vtype(bv, t);
{
    bv->bar();
}

AVirtual::~AVirtual()
/*@ requires 
    AVirtual_vtype(this, &typeid(struct AVirtual)) &*& 
    this->m_a |-> _ &*&
    this->m_bv |-> ?bv &*&
    bv != 0;
@*/
//@ ensures true;
{
  foo();
  bar(m_bv); //~
}

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