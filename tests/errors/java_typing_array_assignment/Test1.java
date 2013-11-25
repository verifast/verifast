public class Test1 {
	
	/**
	 * Sunny day scenario test.
	 */
	public static void main()
	//@ requires true;
	//@ ensures true;
	{
		Test1[] own1;
		Test1[] own2;
		Object[] obj1;
		Object[] obj2;
		int[] int1;
		int[] int2;
		short[] short1;
		short[] short2;
		
		own1 = own2;
		obj1 = obj2;
		int1 = int2;
		short1 = short2;
		
		obj1 = own1;
	}
	
	public void test1()
	//@ requires true;
	//@ ensures true;
	{
		Test1[] own1;
		Object [] obj1;
		own1 = obj1; //~
	}
}
