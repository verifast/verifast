package newmypackage;

import javacard.framework.Shareable;


public interface INewMyAppletPoints extends Shareable {

	byte sharePoints (byte points);
	    //@ requires true;
	    //@ ensures true;

}
