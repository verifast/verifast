import javacard.framework.*;

/*@

predicate length_value_record(list<byte> values, int start; int end) =
    start < length(values) &*&
    0 <= nth(start, values) &*&
    start + 1 + nth(start, values) <= length(values) &*&
    end == start + 1 + nth(start, values);

predicate element(list<byte> values, int offset; byte value) =
    offset < length(values) &*&
    value == nth(offset, values);

@*/

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    /*@
    
    predicate valid() =
        someByteArray |-> ?array &*&
        array_slice(array, 0, array.length, _) &*& 20 <= array.length;
    
    @*/
    
    // Example init data:
    // 5,1,2,3,4,5,  // AID
    // 0,  // info
    // 1,20 // applet data
    public static void install(byte[] array, short offset, byte length)
        /*@
        requires
            class_init_token(MyApplet.class) &*&
            array_slice(array, offset, offset + length, ?values) &*&
            length_value_record(values, 0, ?oInfo) &*&
            length_value_record(values, oInfo, ?oAppData) &*&
            element(values, oAppData, _) &*&
            element(values, oAppData + 1, ?bufferSize) &*&
            20 <= bufferSize &*&
            offset + length <= 32767 &*&
            system();
        @*/
        //@ ensures true;
    {
        //@ init_class(MyApplet.class);
        
        // make all my allocations here, so I do not run
        // out of memory later
        MyApplet theApplet = new MyApplet();
        
        // check incoming parameter data
        //@ open length_value_record(values, 0, oInfo);
        byte iLen = array[offset]; // aid length
        offset = (short)(offset + iLen + 1);
        //@ open length_value_record(values, oInfo, oAppData);
        byte cLen = array[offset]; // info length
        offset = (short)(offset + cLen + 1);
        //@ open element(values, oAppData, _);
        byte aLen = array[offset]; // applet data length
        //@ open element(values, oAppData + 1, _);
        // read first applet data byte
        byte bLen = array[(short)(offset + 1)];
        //@ assert 20 <= bLen;
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close theApplet.valid();
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED); //~allow_dead_code
    }
    
    public boolean select()
        //@ requires current_applet(this) &*& [1/2]this.valid();
        //@ ensures current_applet(this) &*& [1/2]this.valid();
    {
        // selection initialization
        JCSystem.beginTransaction();
        //@ open valid();
        someByteArray[17] = 42; // set selection state
        //@ close valid();
        JCSystem.commitTransaction();
        return true;
    }
    
    public void process(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, ?buffer0) &*& array_slice(buffer0, 0, buffer0.length, _);
        //@ ensures current_applet(this) &*& [1/2]this.valid() &*& APDU(apdu, buffer0) &*& array_slice(buffer0, 0, buffer0.length, _);
    {
        byte[] buffer = apdu.getBuffer();
        // .. process the incoming data and reply
        if (buffer[ISO7816.OFFSET_CLA] == (byte)0) {
            switch (buffer[ISO7816.OFFSET_INS]) {
                case ISO7816.INS_SELECT:
                    // ...
                    // send response data to select command
                    short length = apdu.setOutgoing();
                    byte[] replyData = new byte[10];
                    // assume data containing response bytes in replyData[] array.
                    if (length < 20) ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
                    apdu.setOutgoingLength((short)replyData.length);
                    apdu.sendBytesLong(replyData, (short)0, (short)replyData.length);
                    break;
                //case ...
            }
        }
    }
}
