class A {
  int m_a;

public:
  /*@
  predicate valid() = this != 0 &*& this->m_a |-> ?a &*& a > 0;
  @*/

  A()
      : m_a(1)
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

  void setA(int a)
  //@ requires valid() &*& a > 0;
  //@ ensures valid();
  {
    //@ open valid();
    m_a = a;
    //@ close valid();
  }
};

void setA(A &ref, int a)
//@ requires ref.valid(&typeid(struct A))() &*& a > 0;
//@ ensures ref.valid(&typeid(struct A))();
{
  ref.setA(a);
}

int main()
//@ requires true;
//@ ensures true;
{
  A a;
  setA(a, 4);
  a.setA(2);
}