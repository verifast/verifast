/*@
predicate A_pred(A *a; int i) =
	a != 0 &*& a->a |-> i;
	
lemma_auto void A_pred_inv()
	requires [?f]A_pred(?a, ?i);
	ensures [f]A_pred(a, i) &*& a != 0;
{
	open [f]A_pred(a, i);
	close [f]A_pred(a, i);
}
@*/

struct A {
	int a;

	A(int i) : a(i)
	//@ requires true;
	//@ ensures A_pred(this, i);
	{}

	~A()
	//@ requires A_pred(this, _);
	//@ ensures true;
	{}

	void setA(int i)
	//@ requires A_pred(this, _);
	//@ ensures A_pred(this, i);
	{
		a = i;
	}
};

/*@
predicate B_pred(B *b; int i, int a) =
	b != 0 &*& b->b |-> i &*& A_pred(b, a);
	
lemma_auto void B_pred_inv()
	requires [?f]B_pred(?b, ?i, ?a);
	ensures [f]B_pred(b, i, a) &*& b != 0;
{
	open [f]B_pred(b, i, a);
	close [f]B_pred(b, i, a);
}
@*/

struct B : A {
	int b;

	B() : A(0), b(2)
	//@ requires true;
	//@ ensures B_pred(this, 2, 0);
	{}

	~B()
	//@ requires B_pred(this, _, _);
	//@ ensures true;
	{
	}

	void setB(int i)
	//@ requires this->b |-> _;
	//@ ensures this->b |-> i;
	{
		b = i;
	}
};

/*@
predicate C_pred(C *c; int i, int a) =
	c != 0 &*& c->c |-> i &*& A_pred(c, a);
	
lemma_auto void C_pred_inv()
	requires [?f]C_pred(?c, ?i, ?a);
	ensures [f]C_pred(c, i, a) &*& c != 0;
{
	open [f]C_pred(c, i, a);
	close [f]C_pred(c, i, a);
}
@*/

struct C : A {
	int c;

	C() : A(1), c(3)
	//@ requires true;
	//@ ensures C_pred(this, 3, 1);
	{}

	~C()
	//@ requires C_pred(this, _, _);
	//@ ensures true;
	{}

	void setC(int i)
	//@ requires this->c |-> _;
	//@ ensures this->c |-> i;
	{
		c = i;
	}
};

/*@
predicate D_pred(D *d; int i, int b, int c, int b_a, int c_a) =
	d != 0 &*& d->d |-> i &*& B_pred(d, b, b_a) &*& C_pred(d, c, c_a);
	
lemma_auto void D_pred_inv()
	requires [?f]D_pred(?d, ?i, ?b, ?c, ?b_a, ?c_a);
	ensures [f]D_pred(d, i, b, c, b_a, c_a) &*& d != 0;
{
	open [f]D_pred(d, i, b, c, b_a, c_a);
	close [f]D_pred(d, i, b, c, b_a, c_a);
}
@*/

struct D : B, C {
	int d;

	D() : d(4)
	//@ requires true;
	//@ ensures D_pred(this, 4, 2, 3, 0, 1);
	{}

	~D()
	//@ requires D_pred(this, _, _, _, _, _);
	//@ ensures true;
	{}

	void setD(int i)
	//@ requires this->d |-> _;
	//@ ensures this->d |-> i;
	{
		d = i;
	}
};

int main()
//@ requires true;
//@ ensures true;
{
	D d;
	//@ open B_pred(&d, _, _);
	d.B::setA(-1);
	//@ open C_pred(&d, _, _);
	d.C::setA(-2);
	d.setC(-3);
	d.setB(-4);
	d.setD(-5);
	//@ assert D_pred(&d, -5, -4, -3, -1, -2);
} 