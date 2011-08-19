package wallet;
import javacard.framework.*;

public final class EPhone extends Applet {

    private static final byte EPhone_CLA = (byte)0xB0;

    private static final byte GET_BALANCE = (byte) 0x10;
    private static final byte CREDIT = (byte) 0x20;

    private static final byte SW_EWALLET_AID_NOT_EXIST = (byte) 0x5300;
    private static final byte SW_FAILED_TO_OBTAIN_SIO = (byte) 0x5200;
    private static final byte SW_DOES_NOT_IMPLEMENT_INTERFACE = (byte) 0x2000;
    private static final byte SW_AMOUNT_TO_HIGH = (byte) 0x2222;
    
    static final byte max_transaction_amount = 90;
    private static final short max_balance = 120;
    private static short balance;
    private static byte[] ewallet_aid_bytes; //= new byte[] {(byte)0x15, (byte)0xEF, (byte)0x4D, (byte)0x55, (byte)0x86, (byte)0xB3};
    
    /*@
    predicate valid() = balance |-> ?phone_balance &*& 0 <= phone_balance &*& phone_balance <= max_balance
    			&*& ewallet_aid_bytes |-> ?e_array &*& e_array != null 
    			&*& array_slice(e_array,0,e_array.length,_) &*& e_array.length == 6;
    @*/

    public static void install(byte[] bArray, short bOffset, byte bLength)
    //@ requires balance |-> _ &*& ewallet_aid_bytes |-> _ &*& transient_arrays(?ta) &*& foreach(ta, transient_array);
    //@ ensures true;
    {
        EPhone Ephone = new EPhone();
        Ephone.register();
    }

    protected EPhone() 
    //@ requires balance |-> _ &*& ewallet_aid_bytes |-> _;
    //@ ensures valid();
    {
        balance = 0;
        ewallet_aid_bytes = new byte[] {(byte)0xA8, (byte)0xB6, (byte)0xD1, (byte)0x26, (byte)0xB1, (byte)0xB3};
        //@ close valid();
    }

    public void process(APDU apdu) {
        byte[] abuffer = apdu.getBuffer();

        if(selectingApplet())
            return;

        if(abuffer[ISO7816.OFFSET_CLA] != EPhone_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);

        switch(abuffer[ISO7816.OFFSET_INS]){
            case GET_BALANCE: getBalance(apdu);return;
            case CREDIT: credit(apdu);return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }

    private void credit(APDU apdu)
    //@requires current_applet(this) &*& APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(?as) &*& foreach<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid() &*& mem<Applet>(this,as)==true &*& transient_arrays(?ta) &*& foreach(ta, transient_array);
    //@ensures current_applet(this) &*& APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(as) &*& foreach<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid() &*& transient_arrays(ta) &*& foreach(ta, transient_array);
    {
        byte[] abuffer = apdu.getBuffer();

        byte count = abuffer[ISO7816.OFFSET_LC];
        
        if(count != 1)
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);

        short amount = (short)abuffer[ISO7816.OFFSET_CDATA];
        if(amount < 0)
            ISOException.throwIt(ISO7816.SW_WRONG_DATA);
        if(amount > max_transaction_amount)
            ISOException.throwIt(ISO7816.SW_WRONG_DATA);
            
        ///@ foreach_remove<Applet>(this,as);
        ///@ open semi_valid(this);
        //@ open [1/2]valid();
        short newBalance = (short)(balance + amount);
        //@ close [1/2]valid();
            
        if(newBalance > max_balance)
            ISOException.throwIt(SW_AMOUNT_TO_HIGH);
        ///@ close semi_valid(this);
	///@ foreach_unremove<Applet>(this,as);
	JCSystem.beginTransaction();
        makeBankcardDebit(amount);
        ///@ foreach_remove<Applet>(this,as);
        ///@ open full_valid(this);
        ///@ open semi_valid(this);
        //@ open valid();
        balance = newBalance;
        //@ close valid();
        ///@ close full_valid(this);
        ///@ foreach_unremove<Applet>(this,as);
        JCSystem.commitTransaction();
        ///@ foreach_remove<Applet>(this,as);
        ///@ open semi_valid<Applet>(this);
    }

    private void getBalance(APDU apdu) 
    //@requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(?as) &*& mem<Applet>(this,as)==true &*& foreach<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    //@ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(as) &*& foreach<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    {
    	byte[] abuffer = apdu.getBuffer();

        apdu.setOutgoing();
        apdu.setOutgoingLength((byte)1);

        // place balance in the APDU buffer
        ///@ foreach_remove<Applet>(this,as);
        ///@ open semi_valid(this);
        //@ open [1/2]valid();
        abuffer[0] = (byte)balance;
        //@ close [1/2]valid();
        ///@ close semi_valid(this);
        ///@ foreach_unremove<Applet>(this,as);

        apdu.sendBytes((short)0, (short)1);
    }

    private void makeBankcardDebit(short amount)
    //@ requires 0 <= amount &*& amount <= max_transaction_amount &*& registered_applets(?as) &*& foreach<Applet>(remove<Applet>(this, as),full_valid) &*& this.valid() &*& in_transaction(this, as) &*& mem<Applet>(this,as)==true;
    //@ ensures in_transaction(this, as) &*& registered_applets(as) &*& foreach<Applet>(remove<Applet>(this, as),full_valid) &*& this.valid();
    {
    
    	///@ foreach_remove<Applet>(this, as);
        ///@ open full_valid(this);
    	//@ open valid();
        AID ewallet_aid = JCSystem.lookupAID(ewallet_aid_bytes,(short)0,(byte)ewallet_aid_bytes.length);
	//@ close valid();
        if(ewallet_aid == null)
           ISOException.throwIt(SW_EWALLET_AID_NOT_EXIST);

        Shareable sio = JCSystem.getAppletShareableInterfaceObject(ewallet_aid, (byte)0x01);
	        
        if(sio == null)
          ISOException.throwIt(SW_FAILED_TO_OBTAIN_SIO);

        if(sio instanceof EWalletInterface){
          EWalletInterface WalletInterface = (EWalletInterface)sio;
        
	  ///@ close full_valid(this);
          ///@ foreach_unremove<Applet>(this,as);
	  ///@ close EInterface(EWallet.class)(WalletInterface);  
          byte[] pin = new byte[] {(byte)1,(byte)1,(byte)1,(byte)1};
          ///@ assume (sio.getClass() == EWallet.class);
          // WalletInterface.convertToInstance();
          //@ close full_valid(this);
          //@ foreach_unremove<Applet>(this,as);
          //@ assert (shareable_interface_object(sio.getClass())(sio, ?a));
          //@ foreach_remove<Applet>(a,as);
          //@ open full_valid(a);
          WalletInterface.verify(pin, (short)0, (byte)(short)pin.length);
          WalletInterface.debit((byte)amount);
          //@ close full_valid(a);
          //@ foreach_unremove<Applet>(a, as);
          //@ foreach_remove<Applet>(this, as);
          //@ open full_valid(this);
          
          // WalletInterface.convertFromInstance();
          ///@ assert registered_applets(?as0);
          ///@ assume (as == as0);           
        }else
          ISOException.throwIt(SW_DOES_NOT_IMPLEMENT_INTERFACE);
    }
}