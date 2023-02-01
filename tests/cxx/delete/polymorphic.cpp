struct A
{
  //@ predicate valid() = true;

  A()
  //@ requires true;
  //@ ensures valid() &*& A_vtype(this, thisType);
  {
    //@ close valid();
  }

  virtual ~A()
  //@ requires valid() &*& A_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid();
  }
  
  virtual void foo()
  //@ requires valid();
  //@ ensures valid();
  {}
};

struct B : public A
{
  /*@ predicate valid() =
      this->valid(&typeid(A))() &*& B_bases_constructed(this);
  @*/

  B()
  //@ requires true;
  //@ ensures valid() &*& B_vtype(this, thisType);
  {
    //@ close valid();
  }

  ~B()
  //@ requires valid() &*& B_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid();
  }
  
  void foo()
  //@ requires valid();
  //@ ensures valid();
  {
    //@ open valid();
    A::foo();
    //@ close valid();
  }
};

void dispose(A *a)
//@ requires new_block_A(a, ?t) &*& A_vtype(a, t) &*& a->valid(t)();
//@ ensures true;
{
  delete a;
}

int main()
//@ requires true;
//@ ensures true;
{
  B *b = new B;
  b->foo();
  //@ upcast_new_block((struct A *) b);
  dispose(b);
}