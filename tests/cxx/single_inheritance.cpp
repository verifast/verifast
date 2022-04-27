/*@
predicate A_pred(A *a; int i) =
	a != 0 &*& a->i |-> i;
@*/

struct A {
    int i;

    A(int i) : i(i)
    //@ requires true;
    //@ ensures A_pred(this, i);
    {}
    
    A() : A(0)
    //@ requires true;
    //@ ensures A_pred(this, 0);
    {}
    
    ~A()
    //@ requires A_pred(this, _);
    //@ ensures true;
    {}
    
    void incr()
    //@ requires A_pred(this, ?i);
    //@ ensures A_pred(this, i + 1);
    {
    	++i;
    }
};

/*@
predicate B_pred(B *b; int a_i, int b_i) =
	A_pred(b, a_i) &*& b->i |-> b_i;
@*/

struct B : A {
    int i;
    
    B(int b_i, int a_i) : A(a_i), i(b_i)
    //@ requires true;
    //@ ensures B_pred(this, a_i, b_i);
    {}
    
    B(int i) : i(i)
    //@ requires true;
    //@ ensures B_pred(this, 0, i);
    {}

    B() : B(1, 0)
    //@ requires true;
    //@ ensures B_pred(this, 0, 1);
    {
    }
    
    ~B()
    //@ requires B_pred(this, ?a_i, ?b_i);
    //@ ensures true;
    {
    }
    
    void incr()
    //@ requires B_pred(this, ?a_i, ?b_i);
    //@ ensures B_pred(this, a_i, b_i + 1);
    {
    	++i;
    }
    
    void incr_a()
    //@ requires B_pred(this, ?a_i, ?b_i);
    //@ ensures B_pred(this, a_i + 1, b_i);
    {
      A::incr();
    }
};

/*@
lemma_auto void A_pred_inv()
	requires [?f]A_pred(?a, ?i);
	ensures [f]A_pred(a, i) &*& a != 0;
{
	open [f]A_pred(a, i);
	close [f]A_pred(a, i);
}
	
lemma_auto void B_pred_inv()
	requires [?f]B_pred(?b, ?a_i, ?b_i);
	ensures [f]B_pred(b, a_i, b_i) &*& b != 0;
{
	open [f]B_pred(b, a_i, b_i);
	close [f]B_pred(b, a_i, b_i);
}
@*/

int main()
//@ requires true;
//@ ensures true;
{
    B b;
    B b_(3, 1);
    //@ assert B_pred(&b_, 1, 3);
    B b__(4);
    //@ assert B_pred(&b__, 0, 4);
    //@ assert B_pred(&b, ?a_i, ?b_i);
    b.incr();
    //@ assert B_pred(&b, a_i, b_i + 1);
    b.incr_a();
    //@ assert B_pred(&b, a_i + 1, b_i + 1);
    A &a = b;
    a.incr();
    //@ assert B_pred(&b, a_i + 2, b_i + 1);
    
}