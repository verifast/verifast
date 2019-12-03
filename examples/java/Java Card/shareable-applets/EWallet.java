package wallet;

import javacard.framework.*;

public final class EWallet extends Applet implements EWalletInterface {

    //@ predicate Shareable(Applet owner) = owner == this;
    
    //CLA byte
    static final byte EWallet_CLA =(byte)0x80;

    //Instruction (ins) bytes
    static final byte VERIFY = (byte) 0x20;
    static final byte CREDIT = (byte) 0x30;
    static final byte DEBIT = (byte) 0x40;
    static final byte GET_BALANCE = (byte) 0x50;

    // maximum balance
    static final short MAX_BALANCE = 120;
    // maximum transaction amount
    static final byte MAX_TRANSACTION_AMOUNT = 90;
    // max nb of incorrect tries before pin is blocked
    static final byte PIN_TRY_LIMIT =(byte)0x03;
    // max pin size
    static final byte MAX_PIN_SIZE =(byte)0x08;

    // exceptions
    static final short SW_VERIFICATION_FAILED = 0x6300;
    static final short SW_PIN_VERIFICATION_REQUIRED = 0x6301;
    // amount > MAX_TRANSACTION_AMOUNT or amount < 0
    static final short SW_INVALID_TRANSACTION_AMOUNT = 0x6A83;
    static final short SW_EXCEED_MAXIMUM_BALANCE = 0x6A84;
    static final short SW_NEGATIVE_BALANCE = 0x6A85;

    /* instance variables declaration */
    private static OwnerPIN pin;
    private static short balance;
    private static byte[] pinnb;

    /*@
    predicate valid() = balance |-> ?wallet_balance &*& 0 <= wallet_balance &*& wallet_balance <= MAX_BALANCE 
    			&*& pin |-> ?ownerPin &*& ownerPin != null &*& OwnerPIN(ownerPin,_,_) &*& pinnb |-> ?pinnumber &*& pinnumber != null 
    			&*& array_slice(pinnumber,0,pinnumber.length,_) &*& pinnumber.length <= MAX_PIN_SIZE; 
    @*/

    private EWallet () 
    //@ requires class_init_token(EWallet.class);
    //@ ensures valid();
    {
        //@ init_class();
    	
        pin = new OwnerPIN(PIN_TRY_LIMIT, MAX_PIN_SIZE);
	pinnb = new byte[] {(byte)1,(byte)1,(byte)1,(byte)1};
        //Initialize pin to 1111
        pin.update(pinnb, (short)0, (byte)4);
        balance = 5;
        //@ close valid();
    }

    public static void install(byte[] bArray, short bOffset, byte bLength) 
    //@ requires class_init_token(EWallet.class) &*& system();
    //@ ensures true;
    {
        EWallet wallet = new EWallet();
        wallet.register();
    }

    public boolean select() 
    //@ requires [1/2]this.valid();
    //@ ensures [1/2]this.valid();
    {
        // The applet declines to be selected
        // if the pin is blocked.
        //@ open [1/2]valid();
        if ( pin.getTriesRemaining() == 0 ){
           //@ close [1/2]valid();
	   return false;
	}
	//@ close [1/2]valid();
        return true;
    }

    public void deselect() 
    //@ requires [1/2]this.valid();
    //@ ensures [1/2]this.valid();
    {
        // reset the pins validated flag to unvalidated
        //@ open [1/2]valid();
        pin.reset();
        //@ close [1/2]valid();
    }

    public void process(APDU apdu)
    /*@
    requires
      current_applet(this) &*&
      [1/2]valid() &*&
      apdu != null &*&
      APDU(apdu, ?buffer) &*&
      array_slice(buffer, 0, buffer.length, _);
    @*/
    /*@
    ensures
      current_applet(this) &*&
      [1/2]valid() &*&
      apdu != null &*&
      APDU(apdu, buffer) &*&
      array_slice(buffer, 0, buffer.length, _);
    @*/
    {
        byte[] abuffer = apdu.getBuffer();

        if(selectingApplet())
            return;

        if(abuffer[ISO7816.OFFSET_CLA] != EWallet_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);

        switch (abuffer[ISO7816.OFFSET_INS]) {
        case GET_BALANCE:
            getBalance(apdu);
            return;
        case DEBIT:
            debit(apdu);
            return;
        case CREDIT:
            credit(apdu);
            return;
        case VERIFY:
            verify(apdu);
            return;
        default:
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }

    private void credit(APDU apdu) 
    //@requires current_applet(this) &*& APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& [1/2]this.valid();
    //@ensures current_applet(this) &*& APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& [1/2]this.valid();
    {
    	//@ open [1/2]valid();
        if (!pin.isValidated())
            ISOException.throwIt(SW_PIN_VERIFICATION_REQUIRED);
	//@ close [1/2]valid();
        byte[] abuffer = apdu.getBuffer();

        // read nb of data bytes
        byte numBytes = abuffer[ISO7816.OFFSET_LC];
        // count nb of data bytes read
       
        if ((numBytes != 1))
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);

        // get the credit amount
        short creditAmount = (short)abuffer[ISO7816.OFFSET_CDATA];

        // check the credit amount
        if ((creditAmount > MAX_TRANSACTION_AMOUNT) || (creditAmount < 0))
            ISOException.throwIt(SW_INVALID_TRANSACTION_AMOUNT);
	
	//@ open [1/2]valid();
	short newBalance = (short)(balance + creditAmount);
	//@ close [1/2]valid();
	
	// check the new balance
	if (newBalance > MAX_BALANCE)
	    ISOException.throwIt(SW_EXCEED_MAXIMUM_BALANCE);
        JCSystem.beginTransaction();
        //@ open valid();
        // credit the amount
        balance = newBalance;
        //@ close valid();
        JCSystem.commitTransaction();
    }

    private void debit(APDU apdu) 
    //@ requires current_applet(this) &*& APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& [1/2]this.valid();
    //@ ensures current_applet(this) &*& APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& [1/2]this.valid();
    {
    	//@ open [1/2]valid();
        if (!pin.isValidated())
            ISOException.throwIt(SW_PIN_VERIFICATION_REQUIRED);
        //@ close [1/2]valid();

        byte[] abuffer = apdu.getBuffer();

        byte numBytes = (byte)(abuffer[ISO7816.OFFSET_LC]);

        if (numBytes != 1)
           ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);

        // get debit amount
        byte debitAmount = abuffer[ISO7816.OFFSET_CDATA];

        // check debit amount
        if ((debitAmount > MAX_TRANSACTION_AMOUNT) || (debitAmount < 0))
           ISOException.throwIt(SW_INVALID_TRANSACTION_AMOUNT);

        // check the new balance
        //@ open [1/2]valid();
        short newBalance = (short)(balance - debitAmount);
        //@ close [1/2]valid();
        
        if (newBalance < (short)0)
             ISOException.throwIt(SW_NEGATIVE_BALANCE);

	JCSystem.beginTransaction();
	//@ open valid();
        balance = newBalance;
        //@ close valid();
        JCSystem.commitTransaction();
    }

    private void getBalance(APDU apdu) 
    //@requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(?as) &*& mem<Applet>(this,as)==true &*& foreachp<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    //@ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(as) &*& foreachp<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    {
    	//@ open [1/2]valid();
        if (!pin.isValidated())
            ISOException.throwIt(SW_PIN_VERIFICATION_REQUIRED);
        //@ close [1/2]valid();

        byte[] abuffer = apdu.getBuffer();

        apdu.setOutgoing();
        apdu.setOutgoingLength((byte)1);

        // place balance in the APDU buffer
        //@ open [1/2]valid();
        abuffer[0] = (byte)balance;
        //@ close [1/2]valid();

        apdu.sendBytes((short)0, (short)1);
    }

    private void verify(APDU apdu) 
    //@requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(?as) &*& mem<Applet>(this,as)==true &*& foreachp<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    //@ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(as) &*& foreachp<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    {
        byte[] abuffer = apdu.getBuffer();

        // retrieve nb of bytes read (pin data length)
        byte numBytes = (byte)(abuffer[ISO7816.OFFSET_LC]);

        // check pin
        //@ open [1/2]valid();
        if (numBytes < 0 || pin.check(abuffer, ISO7816.OFFSET_CDATA, numBytes) == false )
            ISOException.throwIt(SW_VERIFICATION_FAILED);
        //@ close [1/2]valid();
    }

    public void verify(byte[] pincode, short offset, byte length) 
    //@ requires array_slice(pincode, 0, pincode.length,_) &*& Shareable(?a) &*& in_transaction(a) &*& a.valid();
    //@ ensures array_slice(pincode, 0, pincode.length,_) &*& Shareable(a) &*& in_transaction(a) &*& a.valid();
    {
    	//@ open Shareable(_);
    	//@ open valid();
    	if (offset < 0 || length < 0 || offset + length > pincode.length)
    	    ISOException.throwIt(ISO7816.SW_WRONG_DATA);
        if ( pin.check(pincode, /*(short)0*/ offset, length) == false )
            ISOException.throwIt(SW_VERIFICATION_FAILED);
        //@ close valid();
    	//@ close Shareable(this);
    }

    public void debit(byte debitAmount) 
    //@ requires 0 <= debitAmount &*& Shareable(?a) &*& in_transaction(a) &*& a.valid();
    //@ ensures Shareable(a) &*& in_transaction(a) &*& a.valid();
    {
    	//@ open Shareable(_);
    	//@ open valid();
        if (!pin.isValidated())
            ISOException.throwIt(SW_PIN_VERIFICATION_REQUIRED);
        //@ close valid();

        // check debit amount
        if ((debitAmount > MAX_TRANSACTION_AMOUNT) || (debitAmount < 0))
           ISOException.throwIt(SW_INVALID_TRANSACTION_AMOUNT);

        // check the new balance
        //@ open valid();
        short newBalance = (short)(balance - debitAmount);
        //@ close valid();
        
        if (newBalance < (short)0)
             ISOException.throwIt(SW_NEGATIVE_BALANCE);

	//@ open valid();
        balance = newBalance;
        //@ close valid();
    	//@ close Shareable(this);
    }

    public Shareable getShareableInterfaceObject(AID clientAID, byte parameter)
    	//@ requires registered_applets(?as) &*& mem<Applet>(this,as) == true &*& AID(clientAID);
    	/*@ ensures registered_applets(as) &*& mem<Applet>(this,as) == true &*& AID(clientAID) &*&
    	        result == null ? true : result.Shareable(?a) &*& mem<Applet>(a, as) == true; @*/
    {
    	if(clientAID == null)
    	    return null;

        byte[] ephone_aid_bytes = new byte[] {(byte)0xA8, (byte)0xB6, (byte)0xD1, (byte)0x26, (byte)0xB1, (byte)0x60};
        
        if(clientAID.equals(ephone_aid_bytes,(short)0,(byte)ephone_aid_bytes.length) == false)
            return null;

        if(parameter != (byte)0x01)
            return null;

	//@ close Shareable(this);
        return (Shareable)this;
    }
}