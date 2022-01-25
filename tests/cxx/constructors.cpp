/*@
predicate MyIntPred(MyInt *mi, int i) =
  mi->_i |-> i;
@*/

struct MyInt {
  int _i;
  
  MyInt() : _i(0)
  //@ requires true;
  //@ ensures MyIntPred(this, 0);
  {
    //@ close MyIntPred(this, this->_i);
  }
  
  ~MyInt()
  //@ requires MyIntPred(this, _);
  //@ ensures true;
  {
    //@ open MyIntPred(this, _);
  }
};

/*@
predicate TestPred(Test *t, int i, int k) =
  t->_j |-> &t->_i &*&
  t->_i |-> i &*&
  t->_k |-> k &*&
  struct_MyInt_padding(?_mi_addr) &*&
  MyIntPred(_mi_addr, _) &*&
  _mi_addr == &t->_mi;
@*/

struct Test {
  int* _j = &_i;
  int _i = 0;
  int _k;
  MyInt _mi;
  
  Test()
  //@ requires true;
  //@ ensures TestPred(this, 1, _);
  {
    _i = 1;
    //@ close TestPred(this, _, _);
  }
  
  Test(int i);
  //@ requires true;
  //@ ensures TestPred(this, i, _);
  
  ~Test()
  //@ requires TestPred(this, _, _);
  //@ ensures true;
  {
    //@ open TestPred(this, _, _);
  }
};

Test::Test(int i) : _i(i)
//@ requires true;
//@ ensures TestPred(this, i, _);
{
  //@ close TestPred(this, i, _);
}

int main()
//@ requires true;
//@ ensures true;
{
  Test *mi = new Test(2);
  Test *mii = new Test;
  delete mi;
  delete mii;
}