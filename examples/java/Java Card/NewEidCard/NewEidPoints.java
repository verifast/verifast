package be.fedict.neweidapplet;

	public class NewEidPoints implements INewEidPoints {

		//@ javacard.framework.Applet applet;
		//@ predicate Shareable(javacard.framework.Applet a) = [_]applet |-> a;

		public byte sharePoints(byte points)
		    //@ requires true;
		    //@ ensures true;
		{
	        return points <= 125 ? (byte) (points + 2) : points;
		}
		
		/*@ lemma void getShareable() requires [_]applet |-> ?a; ensures Shareable(a); {} @*/

	}