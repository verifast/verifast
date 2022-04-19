int &passRef(int &i)
//@ requires integer(&i, ?v);
//@ ensures integer(&i, v) &*& &i == &result;
{
  return i;
}

int unpackRef(int &i)
//@ requires integer(&i, ?v);
//@ ensures integer(&i, v) &*& result == v;
{
  return i;
}

int unpackRefArg(int i)
//@ requires true;
//@ ensures result == i;
{
  return i;
}

int &incr(int &i)
//@ requires integer(&i, ?v);
//@ ensures integer(&i, v + 1) &*& &result == &i;
{
  ++i;
  return i;
}

struct Object {
  int i;
  
  Object() : i(0)
  //@ requires true;
  //@ ensures this->i |-> 0;
  {}
  
  ~Object()
  //@ requires this->i |-> _;
  //@ ensures true;
  {}
};

int main()
//@ requires true;
//@ ensures true;
{
  Object o;
  int i = 0;
  int &iRef = passRef(i);
  int iUnpacked = unpackRef(iRef);
  int iUnpackedArg = unpackRefArg(iRef);
  //@ assert (i == iUnpacked);
  //@ assert (i == iUnpackedArg);
  
  int three = incr(incr(incr(iRef)));
  //@ assert (three == 3);
  //@ assert (three == i);
  
  int &fourRef = incr(i);
  //@ assert (three == 3);
  //@ assert (i == three + 1);
  //@ assert (fourRef == three + 1);
  //@ assert (&fourRef == &i);
  
  ++fourRef;
  //@ assert (three == 3);
  //@ assert (i == three + 2);
  //@ assert (fourRef == three + 2);
  
  Object &oRef = o;
  //@ assert oRef.i == 0;
  o.i = 2;
  //@ assert oRef.i == 2;
}