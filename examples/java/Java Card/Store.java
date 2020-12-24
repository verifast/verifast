package Store;

import javacard.framework.*;

public final class Store extends Applet {
    
    //CLA byte
    private static final byte Store_CLA = (byte) 0xB0;
    //Instruction (ins) bytes
    private static final byte SET = (byte) 0x10;
    private static final byte GET = (byte) 0x20;
    
    //byte array to store data
    private static byte value[];
    
    /*@
    predicate valid() = value |-> ?array &*& array != null &*& array_slice(array, 0, array.length, _) &*& array.length == 5;
    @*/
    
    public static void install(byte[] bArray, short bOffset, byte bLength)
        //@ requires class_init_token(Store.class) &*& system();
        //@ ensures true;
    {
        //@ init_class();
        Store store = new Store();
        store.register();
    }
    
    protected Store()
        //@ requires value |-> _;
        //@ ensures valid();
    {
        value = new byte[5];
        //@ close valid();
    }
    
    public void process(APDU apdu)
        //@ requires [1/2]this.valid() &*& current_applet(this) &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures [1/2]this.valid() &*& current_applet(this) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();
        
        if(selectingApplet())
            return;
        
        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        
        switch(abuffer[ISO7816.OFFSET_INS]) {
            case GET: get(apdu); return;
            case SET: set(apdu); return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }
    
    private final void set(APDU apdu)
        //@ requires APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& current_applet(this) &*& [1/2]valid();
        //@ ensures APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();
        
        //Data received > 5 bytes (length value array) -> exception
        if((abuffer[ISO7816.OFFSET_LC] & 0xff) > 5)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        JCSystem.beginTransaction();
        //@ open valid();
        //Copy received data into value array
        Util.arrayCopy(abuffer, (short)ISO7816.OFFSET_CDATA, value, (short)0, (short)(abuffer[ISO7816.OFFSET_LC] & 0xff));
        //@ close valid();
        JCSystem.commitTransaction();
    }
    
    private void get(APDU apdu)
    //@ requires APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& current_applet(this) &*& [1/2]valid();
    //@ ensures APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();
        
        apdu.setOutgoing();
        apdu.setOutgoingLength(abuffer[ISO7816.OFFSET_LC]);
        
        //@ open [1/2]valid();
        //Send data in value array
        apdu.sendBytesLong(value, (short)0, (short)value.length);
        //@ close [1/2]valid();
    }
    
}
