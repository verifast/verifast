int getRef(int i)
//@ requires true;
//@ ensures i == result;
{
  return i;
}

int unpackRef(int && i)
//@ requires integer(&i, ?v);
//@ ensures integer(&i, v) &*& result == v;
{
  return i;
}

struct Object {
	/*@
	predicate Object(int val) = this->i |-> val;
	@*/

  int i;

  Object() : i(0)
  //@ requires true;
  //@ ensures this->i |-> 0;
  {}

  // Move constructor (int)
  Object(int && i_) : i(i_)
  // @ requires integer(&i_, ?v);
  // @ ensures integer(&i_, v) &*& this->i == i_;
  {}

  // Move constructor
  Object(Object && other) : i(other.i)
  //@ requires other.i |-> ?i_;
  //@ ensures this->i |-> i_ &*& other.i |-> _;
  {}

  // Move assignment operator
	Object & operator=(Object && other)
	//@ requires other.i |-> ?i &*& this->Object(_);
	//@ ensures other.i |-> i &*& this->Object(i) &*& &result == this;
	{
		i = other.i;
		return *this;
	}

  ~Object()
  //@ requires this->i |-> _;
  //@ ensures true;
  {}
};

Object construct()
//@ requires true;
//@ ensures (&result)->i |-> 0 &*& struct_Object_padding(&result);
{
  return Object();
}

int main()
//@ requires true;
//@ ensures true;
{
  int && li = 48;
  int & li2 = li;
  //@ assert (li == 48);
  //@ assert (li2 == 48);

  Object o(0); // Call move constructor (int)
  int && iRef = getRef(42);
  int iUnpacked = unpackRef(42);
  //@ assert (iRef.i == 42);
  //@ assert (iUnpacked == 42);

  // The following expression cannot yet be parsed
  //Object o2(Object(21)); // Call move constructor
  // @ assert (o2.i == 21);

  Object o2;

  o2 = construct(); // Call move assignment operator
  //@ assert (o2.i == 6);
}