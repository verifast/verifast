public class MethodInference{
	public static void main(String[] args)
	//@requires true;
	//@ensures true;
	{
		Boolean a = new Boolean(false);
		Integer b = new Integer(3);
		Integer c = new Integer(5);
		Object o = infer(a,b,c);
		Integer o1 = infer(b,b,c);
	}
	
	public static <T> T infer(T arg1, T arg2, T arg3)
	//@requires true;
	//@ensures true;
	{
        	return arg1;
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
	
	public T get1()
	//@ requires this.f1 |-> ?f;
	//@ ensures result == f;
	{
		return f1;
	}
	
	public V get2()
	//@ requires this.f2 |-> ?f;
	//@ ensures result == f;
	{
		return f2;
	}
}