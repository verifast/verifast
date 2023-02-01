struct A
{
  //@ predicate valid() = true;

  A()
  //@ requires true;
  //@ ensures valid() &*& A_vtype(this, thisType);
  {
    //@ close valid();
  }

  virtual void foo()
  //@ requires valid();
  //@ ensures valid();
  {}

  ~A()
  //@ requires valid() &*& A_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid();
  }
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

  virtual void foo()
  //@ requires valid();
  //@ ensures valid();
  {
    //@ open valid();
    ;
    //@ close valid();
  }

  virtual ~B()
  //@ requires valid() &*& B_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid();
  }
};

void dispose(A *a)
//@ requires new_block_A(a, &typeid(A)) &*& a->valid(&typeid(A))() &*& A_vtype(a, &typeid(A));
//@ ensures true;
{
  delete a;
}

int main()
//@ requires true;
//@ ensures true;
{
  B* b = new B;
  //@ open b->valid();
  //@ upcast_new_block((struct A*) b); //~
  dispose(b);
}