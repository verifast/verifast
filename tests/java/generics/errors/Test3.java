class B<E>{}
class Bar<T> extends B<Integer>{}
class Foo<T> extends B<Boolean>{}

public class Test3{
    
    public void test2()
    //@ requires true;
    //@ ensures true;
    {
    	Boolean boola = new Boolean(false);
		Integer inta = new Integer(3);
		Integer intb = new Integer(5);
    	Integer infer2IntShouldFail = infer2(inta, intb, boola, boola); //~
    }

    public static <T> T infer2(T arg1, T arg2, Object arg3, Integer arg4)
	//@requires true;
	//@ensures true;
	{
        	return arg1;
	}
}