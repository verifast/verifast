class A {
  int m_a;

public:
  /*@
  predicate pos(int a) = this != 0 &*& this->m_a |-> a &*& a >= 0;
  @*/

  A()
      : m_a(1)
  //@ requires true;
  //@ ensures pos(1);
  {
    //@ close pos(1);
  }

  ~A()
  //@ requires pos(_);
  //@ ensures true;
  {
    //@ open pos(_);
  }

  void incr()
  //@ requires pos(?a);
  //@ ensures pos(a + 1);
  {
    //@ open pos(a);
    ++m_a;
    //@ close pos(a + 1);
  }

  int getA()
  //@ requires pos(?a);
  //@ ensures pos(a) &*& result == a;
  {
    //@ open pos(a);
    return m_a;
    //@ close pos(a);
  }

  void setA(int a)
  //@ requires pos(_) &*& a >= 0;
  //@ ensures pos(a);
  {
    //@ open pos(_);
    m_a = a;
    //@ close pos(a);
  }
};

class B {
  int m_b;

public:
  /*@
  predicate neg(int b) = this != 0 &*& this->m_b |-> b &*& b <= 0;
  @*/

  B()
      : m_b(-1)
  //@ requires true;
  //@ ensures neg(-1);
  {
    //@ close neg(-1);
  }

  ~B()
  //@ requires neg(_);
  //@ ensures true;
  {
    //@ open neg(_);
  }

  void decr()
  //@ requires neg(?b);
  //@ ensures neg(b - 1);
  {
    //@ open neg(b);
    --m_b;
    //@ close neg(b - 1);
  }

  int getB()
  //@ requires neg(?b);
  //@ ensures neg(b) &*& result == b;
  {
    //@ open neg(b);
    return m_b;
    //@ close neg(b);
  }

  void setB(int b)
  //@ requires neg(_) &*& b <= 0;
  //@ ensures neg(b);
  {
    //@ open neg(_);
    m_b = b;
    //@ close neg(b);
  }
};

class C : public A, public B {
  int m_c;

public:
  /*@
  predicate opp() =
      this != 0 &*& 
      this->m_c |-> _ &*& 
      this->pos(&typeid(struct A))(?a) &*&
      this->neg(&typeid(struct B))(?b) &*& 
      a + b == 0;
  @*/

  C()
      : m_c(0)
  //@ requires true;
  //@ ensures C_bases_constructed(this) &*& opp();
  {
    //@ close opp();
  }

  ~C()
  //@ requires C_bases_constructed(this) &*& opp();
  //@ ensures true;
  {
    //@ open opp();
  }

  void swap_neg()
  //@ requires C_bases_constructed(this) &*& opp();
  //@ ensures C_bases_constructed(this) &*& opp();
  {
    //@ open opp();
    int a = getA();
    int b = getB();
    //@ open pos(&typeid(struct A))(a);
    //@ close pos(&typeid(struct A))(a);
    setA(-b);
    setB(-a);
    //@ close opp();
  }
};

int main()
//@ requires true;
//@ ensures true;
{
  C c;
  //@ open c.opp();
  c.incr();
  c.decr();
  //@ close c.opp();
  c.swap_neg();
}