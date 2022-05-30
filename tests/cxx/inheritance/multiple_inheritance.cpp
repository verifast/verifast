class A {
    int _a;
public:
	int _pa;

    A(int a) : _a(a), _pa(a)
    //@ requires true;
    //@ ensures this->_a |-> a &*& this->_pa |-> a;
    {}
    
    ~A()
    //@ requires this->_a |-> _ &*& this->_pa |-> _;
    //@ ensures true;
    {}
    
    int foo() const
    //@ requires this->_a |-> ?a;
    //@ ensures this->_a |-> a &*& result == a;
    {
        return _a;
    }
    
    int a()
    //@ requires this->_a |-> ?a;
    //@ ensures this->_a |-> a &*& result == a;
    {
    	return foo();
    }
};

class B {
	int _b;
public:
	int _pb;

	B(int b) : _b(b), _pb(b)
	//@ requires true;
	//@ ensures this->_b |-> b &*& this->_pb |-> b;
	{}
	
	~B()
	//@ requires this->_b |-> _ &*& this->_pb |-> _;
	//@ ensures true;
	{}
	
	int foo() const
	//@ requires this->_b |-> ?b;
	//@ ensures this->_b |-> b &*& result == b;
	{
		return _b;
	}
	
	int b() const
	//@ requires this->_b |-> ?b;
	//@ ensures this->_b |-> b &*& result == b;
	{
		return foo();
	}
};

class C : public A, public B {
	int _c;
public:
	int _pc;

	C(int c) : A(3), B(7), _c(c), _pc(c)
	//@ requires true;
	//@ ensures A__a(this, 3) &*& A__pa(this, 3) &*& B__b(this, 7) &*& B__pb(this, 7) &*& this->_c |-> c &*& this->_pc |-> c &*& (struct A *) this != 0 &*& (struct B *) this != 0;
	{}
	
	~C()
	//@ requires A__a(this, _) &*& A__pa(this, _) &*& B__b(this, _) &*& B__pb(this, _) &*& this->_c |-> _ &*& this->_pc |-> _;
	//@ ensures true;
	{}
	
	int foo() const
	//@ requires this->_c |-> ?c;
	//@ ensures this->_c |-> c &*& result == c;
	{
		return _c;
	}
};

int main()
//@ requires true;
//@ ensures true;
{
	C c_obj(0);
	B &b_obj = c_obj;
	A &a_obj = c_obj;
	
	int a0 = c_obj.A::foo();
	int a1 = a_obj.foo();
	int a2 = c_obj.a();
	//@ assert a0 == a1 && a1 == a2 && a0 == 3;
	
	int b0 = c_obj.B::foo();
	int b1 = b_obj.foo();
	int b2 = c_obj.b();
	//@ assert b0 == b1 && b1 == b2 && b0 == 7;
	
	int c = c_obj.foo();
	//@ assert c == 0;
	
	c_obj._pb = -3;
	c_obj._pa = -1;
	//@ assert b_obj._pb |-> -3;
	//@ assert a_obj._pa |-> -1;
}