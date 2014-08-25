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
    //@ requires class_init_token(EPhone.class) &*& system();
    //@ ensures true;
    {
        EPhone Ephone = new EPhone();
        Ephone.register();
    }

    protected EPhone() 
    //@ requires class_init_token(EPhone.class);
    //@ ensures valid();
    {
        //@ init_class();
        balance = 0;
        ewallet_aid_bytes = new byte[] {(byte)0xA8, (byte)0xB6, (byte)0xD1, (byte)0x26, (byte)0xB1, (byte)0xB3};
        //@ close valid();
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

        if(abuffer[ISO7816.OFFSET_CLA] != EPhone_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);

        switch(abuffer[ISO7816.OFFSET_INS]){
            case GET_BALANCE: getBalance(apdu);return;
            case CREDIT: credit(apdu);return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }

    private void credit(APDU apdu)
    //@requires current_applet(this) &*& APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& [1/2]this.valid();
    //@ensures current_applet(this) &*& APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& [1/2]this.valid();
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
            
        //@ open [1/2]valid();
        short newBalance = (short)(balance + amount);
        //@ close [1/2]valid();
            
        if(newBalance > max_balance)
            ISOException.throwIt(SW_AMOUNT_TO_HIGH);
	JCSystem.beginTransaction();
        makeBankcardDebit(amount);
        //@ open valid();
        balance = newBalance;
        //@ close valid();
        JCSystem.commitTransaction();
    }

    private void getBalance(APDU apdu) 
    //@requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(?as) &*& mem<Applet>(this,as)==true &*& foreachp<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    //@ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& registered_applets(as) &*& foreachp<Applet>(remove<Applet>(this, as),semi_valid) &*& [1/2]this.valid();
    {
    	byte[] abuffer = apdu.getBuffer();

        apdu.setOutgoing();
        apdu.setOutgoingLength((byte)1);

        // place balance in the APDU buffer
        //@ open [1/2]valid();
        abuffer[0] = (byte)balance;
        //@ close [1/2]valid();

        apdu.sendBytes((short)0, (short)1);
    }

    private void makeBankcardDebit(short amount)
    //@ requires 0 <= amount &*& amount <= max_transaction_amount &*& this.valid() &*& in_transaction(this);
    //@ ensures in_transaction(this) &*& this.valid();
    {
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
        
          byte[] pin = new byte[] {(byte)1,(byte)1,(byte)1,(byte)1};
          //@ close full_valid(this);
          //@ assert registered_applets(?as);
          //@ foreachp_unremove<Applet>(this,as);
          //@ mem_registered_applets_is(this);
          //@ assert sio.Shareable(?a);
          //@ set_current_applet(a);
          //@ foreachp_remove<Applet>(a,as);
          //@ open full_valid(a);
          WalletInterface.verify(pin, (short)0, (byte)(short)pin.length);
          WalletInterface.debit((byte)amount);
          //@ close full_valid(a);
          //@ open in_transaction0(a);
          //@ assert registered_applets(?as1);
          //@ foreachp_unremove<Applet>(a, as1);
          //@ is_registered_applets_mem(this);
          //@ set_current_applet(this);
          //@ foreachp_remove<Applet>(this, as1);
          //@ open full_valid(this);
          
        }else
          ISOException.throwIt(SW_DOES_NOT_IMPLEMENT_INTERFACE);
    }
}