package newepurse;

import javacard.framework.*;

import org.globalplatform.GPSystem;


public class EPurseServicesCredit implements IEPurseServicesCredit {

    private NewEPurseApplet epurseApplet;

    //@ predicate Shareable(NewEPurseApplet a) = epurseApplet |-> a;

    EPurseServicesCredit(NewEPurseApplet epurseApplet)
        //@ requires true;
        //@ ensures Shareable(epurseApplet);
    {
	this.epurseApplet = epurseApplet;
    }


    public void charge(short amount)
        //@ requires Shareable(?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures Shareable(a) &*& in_transaction(a) &*& a.valid();
    {
	// application state checking
	// Rational: when the applet is LOCKED, it cannot be selected,
	// but it can be accessed trough shared method calls.
	if (GPSystem.getCardContentState() == GPSystem.APPLICATION_LOCKED)
	    ISOException.throwIt(NewEPurseApplet.SW_INVALID_STATE);
	short clientId;
	// client registration checking
	AID clientAID = JCSystem.getPreviousContextAID();
	if ((clientId = epurseApplet.searchClientAID(clientAID)) == -1)
	    ISOException.throwIt(NewEPurseApplet.SW_INVALID_CLIENT);
	short clientLimit = epurseApplet.getClientLimit(clientId);
	// client limit checking
	if (amount > clientLimit) 
	    ISOException.throwIt(NewEPurseApplet.SW_CLIENT_LIMIT_EXCEEDED);
	// service delivering
	epurseApplet.charge(amount);
    }
    
    public void transaction(short amount)
        //@ requires Shareable(?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures Shareable(a) &*& in_transaction(a) &*& a.valid();
    {
       	// application state checking
       	// Rational: when the applet is LOCKED, it cannot be selected,
       	// but it can be accessed trough shared method calls.
       	if (GPSystem.getCardContentState() == GPSystem.APPLICATION_LOCKED)
       	    ISOException.throwIt(NewEPurseApplet.SW_INVALID_STATE);
       	short clientId;
       	// client registration checking
       	AID clientAID = JCSystem.getPreviousContextAID();
       	if ((clientId = epurseApplet.searchClientAID(clientAID)) == -1)
       	    ISOException.throwIt(NewEPurseApplet.SW_INVALID_CLIENT);
       	short clientLimit = epurseApplet.getClientLimit(clientId);
       	// client limit checking
       	if (amount > clientLimit) 
       	    ISOException.throwIt(NewEPurseApplet.SW_CLIENT_LIMIT_EXCEEDED);
       	// service delivering
       	epurseApplet.transaction(amount);
    }
    

}
