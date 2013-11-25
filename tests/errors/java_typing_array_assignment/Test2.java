/**
 * See Test1.java
 *
 * (we have to split to multiple files because VeriFast
 * does not support multiple allow-fails (even when they
 * are in multiple methods).
 */

public class Test2 {
	
	public void test2()
	//@ requires true;
	//@ ensures true;
	{
		int[] int1;
		short [] short1;
		int1 = short1; //~ should-fail
	}
}

