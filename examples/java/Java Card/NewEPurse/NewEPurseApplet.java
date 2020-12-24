package newepurse;

import javacard.framework.*;

import org.globalplatform.GPSystem;
import org.globalplatform.SecureChannelx;

/*@

fixpoint boolean non_null(list<Object> os) {
    switch (os) {
        case nil: return true;
        case cons(o0, os0): return o0 != null && non_null(os0);
    }
}

lemma void non_null_nth(list<Object> os, int i)
    requires 0 <= i &*& i < length(os) &*& non_null(os) == true;
    ensures nth(i, os) != null;
{
    switch (os) {
        case nil:
        case cons(o0, os0):
            if (i != 0)
                non_null_nth(os0, i - 1);
    }
}

@*/

public final class NewEPurseApplet extends Applet {

    /*** Constants ***/
    
    public static final byte EPURSE_CLA = ISO7816.CLA_ISO7816;

    public static final byte GET_BALANCE_INS = 0x01;
    public static final byte CREDIT_INS = 0x02;
    public static final byte DEBIT_INS = 0x03;
    public static final byte SET_LIMIT_INS = 0x04;
    public static final byte ADD_CLIENT_APPLET_INS = 0x05;
    
    public static final short SW_INVALID_AID = 0x42;
    public static final short SW_CLIENT_CAPACITY_EXCEEDED = 0x43;
    public static final short SW_INVALID_STATE = 0x44;
    public static final short SW_INVALID_CLIENT = 0x45;
    public static final short SW_INVALID_CLIENT_LIMIT = 0x46;
    public static final short SW_CLIENT_LIMIT_EXCEEDED = 0x47;

    private static final short INITIAL_BALANCE_LIMIT = 100;
    private static final short CLIENT_NUMBER_LIMIT = 10;


    /*** Instance variables ***/
    
    private short balance;
    private short limit;

    private AID[] clientAIDs;
    private short[] clientLimits;
    private short clientNumber;

    private byte[] workingBuffer;

    /*@
    predicate valid() =
        balance |-> ?balance_ &*&
        limit |-> ?limit_ &*&
        0 <= balance_ &*& balance_ <= limit_ &*&
        clientAIDs |-> ?clientAIDs_ &*& clientAIDs_.length == CLIENT_NUMBER_LIMIT &*&
        clientLimits |-> ?clientLimits_ &*& clientLimits_.length == CLIENT_NUMBER_LIMIT &*&
        clientNumber |-> ?clientNumber_ &*&
        array_slice(clientAIDs_, 0, clientNumber_, ?activeAids) &*& non_null(activeAids) == true &*&
        array_slice(clientAIDs_, clientNumber_, CLIENT_NUMBER_LIMIT, _) &*&
        array_slice(clientLimits_, 0, CLIENT_NUMBER_LIMIT, ?limits) &*&
        workingBuffer |-> ?workingBuffer_ &*& is_transient_byte_array(workingBuffer_) == true &*& workingBuffer_.length == 16;
    @*/

    /*** Constructor ***/

    /**
     * Constructor of the EPurse applet.
     * This constructor allocates all the memory to be used by the EPurse applet.
     */
    
    private NewEPurseApplet()
        //@ requires system();
        //@ ensures system() &*& valid();
    {
	balance = 0;
	limit = INITIAL_BALANCE_LIMIT;
	clientAIDs = new AID[CLIENT_NUMBER_LIMIT];
	clientLimits = new short[CLIENT_NUMBER_LIMIT];
	clientNumber = 0;
	workingBuffer = JCSystem.makeTransientByteArray((short) 16, JCSystem.CLEAR_ON_DESELECT);
	//@ close valid();
    }
    

    /*** Methods ***/
        
    /**
     * Invoked by the Card Manager to install the EPurse applet.
     * Allocates necessary memory for use by the EPurse applet.
     *
     * @param bArray - the array containing installation parameters
     * @param sOffset - the starting offset in bArray
     * @param bLength - the length in bytes of the parameter data in bArray
     */    

    public static void install(byte[] bArray, short sOffset, byte bLength)
        //@ requires system() &*& array_slice(bArray, sOffset, sOffset + bLength, _);
        //@ ensures true;
    {
        new NewEPurseApplet().register(bArray, sOffset, bLength);
    }
    
    /** 
     * Process the APDU commands.
     *
     * @param oApdu the APDU object
     * @exception ISO7816.SW_CLA_NOT_SUPPORTED
     * @exception ISO7816.SW_INS_NOT_SUPPORTED
     * TODO: complete
     */
    
    public void process(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] apduBuffer = apdu.getBuffer();
	// APDU header processing
	// CLA checking
	if (apduBuffer[ISO7816.OFFSET_CLA] != EPURSE_CLA)
	    ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
	// P1 and P2 checking
	if (apduBuffer[ISO7816.OFFSET_P1] != 0 || apduBuffer[ISO7816.OFFSET_P2] != 0)
	    ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
	// INS checking and dispatching
	switch (apduBuffer[ISO7816.OFFSET_INS]) {
	case GET_BALANCE_INS :
	    getBalance(apdu);
	    break;
	case CREDIT_INS :
	    credit(apdu);
	    break;
	case DEBIT_INS :
	    debit(apdu);
	    break;
	case SET_LIMIT_INS :
	    setLimit(apdu);
	    break;
	case ADD_CLIENT_APPLET_INS :
	    SecureChannelx sc = (SecureChannelx) GPSystem.getSecureChannel();
	    sc.setSecurityLevel((byte) 0x83);
	    short lc_encrypted = sc.processSecurity(apdu);
	    //@ assume(0 <= lc_encrypted && lc_encrypted <= apduBuffer.length - ISO7816.OFFSET_CDATA);
	    short lc = sc.decryptData(apduBuffer, ISO7816.OFFSET_CDATA, lc_encrypted);
	    sc.unwrap(apduBuffer, ISO7816.OFFSET_CDATA, lc);
	    addClientApplet(apdu);
	    break;
	default :
	    ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
	}
    }
    

    private void getBalance(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
	byte[] apduBuffer = apdu.getBuffer();
	// LC checking
        if (apduBuffer[ISO7816.OFFSET_LC] != 0)
	    ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
	
	//@ open valid();
	//@ transient_byte_arrays_mem(workingBuffer);
	//@ assert transient_byte_arrays(?as);
	//@ foreachp_remove(workingBuffer, as);
	//@ open transient_byte_array(workingBuffer);
	Util.setShort(workingBuffer, (short) 0, balance);
        Util.arrayCopy(workingBuffer, (short) 0, apduBuffer, ISO7816.OFFSET_CDATA, (short) 2);
        //@ close transient_byte_array(workingBuffer);
        //@ foreachp_unremove(workingBuffer, as);
        
        apdu.setOutgoingAndSend(ISO7816.OFFSET_CDATA, (short) 2);
    }

    private void credit(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
	byte[] apduBuffer = apdu.getBuffer();
	// LC checking
	if (apduBuffer[ISO7816.OFFSET_LC] != 2)
	    ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
	apdu.setIncomingAndReceive();
	
	//@ open valid();
	//@ transient_byte_arrays_mem(workingBuffer);
	//@ assert transient_byte_arrays(?as);
	//@ foreachp_remove(workingBuffer, as);
	//@ open transient_byte_array(workingBuffer);
        Util.arrayCopy(apduBuffer, ISO7816.OFFSET_CDATA, workingBuffer, (short) 0, (short) 2);
	short amount = Util.getShort(workingBuffer, (short) 0);
        //@ close transient_byte_array(workingBuffer);
        //@ foreachp_unremove(workingBuffer, as);
        
	// BUG: if (amount <= (short)0 || (short) (balance + amount) > limit) // Overflow!
	if (amount <= (short)0 || (short)(limit - amount) < balance)
	    ISOException.throwIt(ISO7816.SW_DATA_INVALID);
	JCSystem.beginTransaction(); // Added for VeriFast
	balance += amount;
	JCSystem.commitTransaction(); // Added for VeriFast
    }

    private void debit(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
	byte[] apduBuffer = apdu.getBuffer();
	// LC checking
	if (apduBuffer[ISO7816.OFFSET_LC] != 2)
	    ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
	apdu.setIncomingAndReceive();
	
	//@ open valid();
	//@ transient_byte_arrays_mem(workingBuffer);
	//@ assert transient_byte_arrays(?as);
	//@ foreachp_remove(workingBuffer, as);
	//@ open transient_byte_array(workingBuffer);
        Util.arrayCopy(apduBuffer, ISO7816.OFFSET_CDATA, workingBuffer, (short) 0, (short) 2);
	short amount = Util.getShort(workingBuffer, (short) 0);
        //@ close transient_byte_array(workingBuffer);
        //@ foreachp_unremove(workingBuffer, as);
	
	JCSystem.beginTransaction(); // Added for VeriFast
	debit(amount);
	JCSystem.commitTransaction(); // Added for VeriFast
    }

    void debit(short amount)
        //@ requires valid();
        //@ ensures valid();
    {
	if (amount <= (short)0 || (short)(balance - amount) < (short)0)
	    ISOException.throwIt(ISO7816.SW_DATA_INVALID);
	balance -= amount;
    }
    
    void transaction(short amount)
        //@ requires valid();
        //@ ensures valid();
    {
    	if (amount <= (short)0 || (short)(balance - amount) < (short)0)
    	    ISOException.throwIt(ISO7816.SW_DATA_INVALID);
    	balance -= amount;      
    }
    
    void charge(short amount)
        //@ requires valid();
        //@ ensures valid();
    {
    	//BUG: if (amount <= (short)0 || (short)(balance - amount) < (short)0) 
	if (amount <= (short)0 || (short)(limit - amount) < balance)
	    ISOException.throwIt(ISO7816.SW_DATA_INVALID);
    	balance += amount;
    }

    private void setLimit(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
	byte[] apduBuffer = apdu.getBuffer();
	// LC checking
	if (apduBuffer[ISO7816.OFFSET_LC] != 2)
	    ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
	apdu.setIncomingAndReceive();
	
	//@ open valid();
	//@ transient_byte_arrays_mem(workingBuffer);
	//@ assert transient_byte_arrays(?as);
	//@ foreachp_remove(workingBuffer, as);
	//@ open transient_byte_array(workingBuffer);
        Util.arrayCopy(apduBuffer, ISO7816.OFFSET_CDATA, workingBuffer, (short) 0, (short) 2);
	short newLimit = Util.getShort(workingBuffer, (short) 0);
        //@ close transient_byte_array(workingBuffer);
        //@ foreachp_unremove(workingBuffer, as);
	
	if (newLimit <= 0 || balance > newLimit)
	    ISOException.throwIt(ISO7816.SW_DATA_INVALID);
	
	JCSystem.beginTransaction(); // Added for VeriFast
	limit = newLimit;
	JCSystem.commitTransaction(); // Added for VeriFast
    }

    private void addClientApplet(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
	byte[] apduBuffer = apdu.getBuffer();
	// LC checking
	byte lc = apduBuffer[ISO7816.OFFSET_LC];
	if (lc < 8 || lc > 19)
	    ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
	apdu.setIncomingAndReceive();
	byte aidLength = apduBuffer[ISO7816.OFFSET_CDATA];
	if (lc != aidLength + 3)
	    ISOException.throwIt(ISO7816.SW_DATA_INVALID);
	
	//@ open valid();
	//@ transient_byte_arrays_mem(workingBuffer);
	//@ assert transient_byte_arrays(?as);
	//@ foreachp_remove(workingBuffer, as);
	//@ open transient_byte_array(workingBuffer);
	Util.arrayCopy(apduBuffer, (short) (ISO7816.OFFSET_CDATA + 1), 
		       workingBuffer, (short) 0, aidLength);
	AID clientAID = JCSystem.lookupAID(workingBuffer, (short) 0, aidLength);
	if (clientAID == null)
	    ISOException.throwIt(SW_INVALID_AID);
	Util.arrayCopy(apduBuffer, (short) (ISO7816.OFFSET_CDATA + 1 + aidLength), 
		       workingBuffer, (short) 0, (short) 2);
	short clientLimit = Util.getShort(workingBuffer, (short) 0);
        //@ close transient_byte_array(workingBuffer);
        //@ foreachp_unremove(workingBuffer, as);

	if (clientLimit < 0 || clientLimit > limit)
	    ISOException.throwIt(SW_INVALID_CLIENT_LIMIT);
	short clientId = 0;
	JCSystem.beginTransaction(); // Added for VeriFast
	//@ open [1/2]valid();
	if (clientNumber == clientAIDs.length) {
	    if ((clientId = searchClientAID(clientAID)) == -1)
		ISOException.throwIt(SW_CLIENT_CAPACITY_EXCEEDED);
	    clientLimits[clientId] = clientLimit;
	} else if ((clientId = searchClientAID(clientAID)) == -1) {
	    clientAIDs[clientNumber] = clientAID;
	    clientLimits[clientNumber] = clientLimit;
	} else {
	    clientLimits[clientId] = clientLimit;	    
	}
	// BUG: Does not update clientNumber!
	JCSystem.commitTransaction(); // Added for VeriFast
    }

    short searchClientAID(AID clientAID)
        //@ requires [?f]clientNumber |-> ?n &*& [f]clientAIDs |-> ?aids &*& [f]array_slice(aids, 0, n, ?aidsElems) &*& non_null(aidsElems) == true;
        //@ ensures [f]clientNumber |-> n &*& [f]clientAIDs |-> aids &*& [f]array_slice(aids, 0, n, aidsElems) &*& result == -1 ? true : 0 <= result &*& result < n;
    {
	for (short i = 0; i < clientNumber; i++)
	    //@ invariant [f]clientNumber |-> n &*& [f]clientAIDs |-> aids &*& [f]array_slice(aids, 0, n, aidsElems) &*& 0 <= i;
	{
	    //@ non_null_nth(aidsElems, i);
	    if (clientAIDs[i].equals(clientAID))
		return i;
	}
	return -1;
    }

    short getClientLimit(short clientId)
        //@ requires [?f]clientLimits |-> ?limits &*& [f]array_slice(limits, 0, CLIENT_NUMBER_LIMIT, ?ls) &*& 0 <= clientId &*& clientId < CLIENT_NUMBER_LIMIT;
        //@ ensures [f]clientLimits |-> limits &*& [f]array_slice(limits, 0, CLIENT_NUMBER_LIMIT, ls);
    {
	return clientLimits[clientId];
    }

    public Shareable getShareableInterfaceObject(AID clientAID, byte parameter)
        //@ requires registered_applets(?as) &*& [1/2]this.valid() &*& AID(clientAID) &*& mem<Applet>(this, as) == true;
        //@ ensures registered_applets(as) &*& [1/2]this.valid() &*& AID(clientAID) &*& result == null ? true : result.Shareable(?a) &*& mem<Applet>(a, as) == true;
    {
	// Security: when the applet is LOCKED, it cannot be selected,
	// but it can be accessed trough method calls.
	if (GPSystem.getCardContentState() == GPSystem.APPLICATION_LOCKED)
	    return null;
	// Security: client AID verification
	if (searchClientAID(clientAID) == -1)
	    return null;
	if (parameter > (byte)1) return null;
	if (parameter == (byte)0)return new EPurseServicesDebit(this);
	else return new EPurseServicesCredit(this);
    }

}
