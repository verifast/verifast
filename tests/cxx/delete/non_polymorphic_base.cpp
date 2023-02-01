struct A
{
  //@ predicate valid() = true;

  A()
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

  virtual ~B()
  //@ requires valid() &*& B_vtype(this, thisType);
  //@ ensures true;
  {
    //@ open valid();
  }
};

void dispose(A *a)
//@ requires a->valid() &*& new_block_A(a);
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