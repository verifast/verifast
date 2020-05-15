import java.util.Arrays;

public class QualifiedGenericMethodCall {

	public static <T,V> V usefulMethod(T arg, V arg2)
	//@ requires true;
	//@ ensures true;
	{
		return arg2;
	}
	
	public static void main(String[] args) 
	//@ requires true;
	//@ ensures true;
	{
		// Qualified call to static parameterised method:
		// Type arguments explicitly provided.
		Integer[] a = {new Integer(1), new Integer(2)};
		Boolean b = new Boolean(true);
		QualifiedGenericMethodCall.<Integer[], Boolean>usefulMethod(a, b);
		
		Integer c = new Integer(3);
		
		Bar myBar = new Bar();
		myBar.<Integer, Boolean>foo(c,b);
	}
}

public class Bar {
    public <T> void foo(int x, T y) 
    //@ requires true;
    //@ ensures true;
    {  
    	this.<Integer,T>foo(x,y);
    }
    public <T, U> void foo(T x, U y)
    //@ requires true;
    //@ ensures true;
    {  }
}