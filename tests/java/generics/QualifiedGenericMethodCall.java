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
	}
}