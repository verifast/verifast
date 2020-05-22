public class DiamondOperator{
	
	public static void main(String[] args)
	//@requires true;
	//@ensures true;
	{
		// Base case: Constructor, type inference through the target
		Other<Integer,Boolean> o = new Other< >();
		Integer f1 = o.get1();
		Boolean f2 = o.get2();
		
		assert f1 == null && f2 == null;
		
		// Case 1: Constructor with arguments
		Integer a = new Integer(2);
		Boolean b = new Boolean(true);
		Other<Integer,Boolean> o1 = new Other< >(a,b);
		f1 = o1.get1();
		f2 = o1.get2();
		
		Other<Boolean,Integer> invert = new Other< >(b,a);
		f2 = invert.get1();
		f1 = invert.get2();
		
		Other<Boolean,Integer> abba = new Other< >(b,b,a);
		
		assert f1 == a && f2 == b;
		
		f1 = o1.get2();  //~
	}
}

public class Other<T,V>{
	T f1;
	V f2;
	
	public Other()
	//@requires true;
	//@ensures this.f1 |-> null &*& this.f2 |-> null;
	{ 
		f1 = null;
		f2 = null;
	}
	
	public Other(T arg1, V arg2)
	//@requires true;
	//@ensures this.f1 |-> arg1 &*& this.f2 |-> arg2;
	{
		f1 = arg1;
		f2 = arg2;
	}
	
	public Other(T arg1, T arg2, V arg3)
	//@requires true;
	//@ensures this.f1 |-> arg1 &*& this.f2 |-> arg3;
	{
		f1 = arg1;
		f2 = arg3;
	}
	
	public T get1()
	//@ requires this.f1 |-> ?f;
	//@ ensures result == f &*& this.f1 |-> f;
	{
		return f1;
	}
	
	public V get2()
	//@ requires this.f2 |-> ?f;
	//@ ensures result == f &*& this.f2 |-> f;
	{
		return f2;
	}
}