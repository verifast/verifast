class A {
protected:
  int m_i;

public:
  /*@
  predicate valid() = this != 0 &*& this->m_i |-> ?i &*& i >= 0;
  @*/

  A() : m_i(0)
  //@ requires true;
  //@ ensures valid();
  {
    //@ close valid();
  }

  ~A()
  //@ requires valid();
  //@ ensures true;
  {
    //@ open valid();
  }

  int getI()
  //@ requires [?f]valid();
  //@ ensures [f]valid() &*& result >= 0;
  {
    //@ open [f]valid();
    return m_i;
    //@ close [f]valid();
  }
};

class B : public A {
  int m_j;

public:
  /*@
  predicate valid() = 
    this != 0 &*& 
    this->valid(&typeid(struct A))() &*&
    this->m_j |-> ?j &*& 
    j >= 0;
  @*/

  B() : m_j(0)
  //@ requires true;
  //@ ensures B_bases_constructed(this) &*& valid();
  {
    //@ close valid();
  }

  ~B()
  //@ requires B_bases_constructed(this) &*& valid();
  //@ ensures true;
  {
    //@ open valid();
  }

  int getJ()
  //@ requires [?f]B_bases_constructed(this) &*& [?ff]valid();
  //@ ensures [f]B_bases_constructed(this) &*& [ff]valid() &*& result >= 0;
  {
    //@ open [ff]valid();
    return m_j;
    //@ close [ff]valid();
  }

  void setI(int i)
  //@ requires [?f]B_bases_constructed(this) &*& valid() &*& i >= 0;
  //@ ensures [f]B_bases_constructed(this) &*& valid();
  {
    //@ open valid();
    //@ open valid(&typeid(struct A))();
    m_i = i;
    //@ close valid(&typeid(struct A))();
    //@ close valid();
  }
};

int main()
//@ requires true;
//@ ensures true;
{
  B b;
  int k = b.getJ();
  b.setI(k);
}