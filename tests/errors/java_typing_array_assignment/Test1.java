public class Test1 {
	
	/**
	 * Sunny day scenario test.
	 */
	public static void main()
	//@ requires true;
	//@ ensures true;
	{
		Test1[] own1 = null;
		Test1[] own2 = null;
		Object[] obj1 = null;
		Object[] obj2 = null;
		int[] int1 = null;
		int[] int2 = null;
		short[] short1 = null;
		short[] short2 = null;
		
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
