package newmypackage;

	public class NewMyAppletPoints implements INewMyAppletPoints {

		//@ javacard.framework.Applet applet;
		//@ predicate Shareable(javacard.framework.Applet a) = [_]applet |-> a;
		
		public byte sharePoints(byte points) 
		  //@ requires true;
                  //@ ensures true;
		{
	        return points <= 124 ? (byte) (points + 3) : points;
		}
		
		//@ lemma void getShareable() requires [_]applet |-> ?a; ensures Shareable(a); {}

	}