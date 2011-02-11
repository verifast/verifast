import javacard.framework.*;

/*@

predicate length_value_record(byte[] array, int start, int end) =
    array[start] |-> ?length &*& 0 <= length &*&
    end == start + 1 + length &*&
    array_slice(array, start + 1, end, _);

@*/

public final class MyApplet extends Applet {
    static byte someByteArray[];
    
    /*@
    
    predicate valid() =
        someByteArray |-> ?array &*&
        array_slice(array, 0, array.length, _) &*& 20 <= array.length;
    
    @*/
    
    public static void install(byte[] array, short offset, byte length) throws ISOException
        /*@
        requires
            someByteArray |-> _ &*& // TODO: Eliminate this
            length_value_record(array, offset, ?infoStart) &*&
            length_value_record(array, infoStart, ?appletDataStart) &*&
            array[appletDataStart] |-> ?appletDataLength &*&
            array[appletDataStart + 1] |-> ?bufferSize &*& 20 <= bufferSize &*&
            appletDataStart + 1 <= 32767;
        @*/
        //@ ensures true;
    {
        // make all my allocations here, so I do not run
        // out of memory later
        MyApplet theApplet = new MyApplet();
        
        // check incoming parameter data
        //@ open length_value_record(array, offset, infoStart);
        byte iLen = array[offset]; // aid length
        //@ open length_value_record(array, infoStart, appletDataStart);
        offset = (short)(offset + iLen + 1);
        byte cLen = array[offset]; // info length
        offset = (short)(offset + cLen + 1);
        byte aLen = array[offset]; // applet data length
        // read first applet data byte
        byte bLen = array[(short)(offset + 1)];
        if (bLen != 0) {
            someByteArray = new byte[bLen];
            //@ close theApplet.valid();
            theApplet.register();
            return;
        } else
            ISOException.throwIt(ISO7816.SW_FUNC_NOT_SUPPORTED);
    }
    
    public boolean select()
        //@ requires current_applet(this) &*& [1/2]valid();
        //@ ensures current_applet(this) &*& [1/2]valid();
    {
        // selection initialization
        JCSystem.beginTransaction();
        //@ open valid();
        someByteArray[17] = 42; // set selection state
        //@ close valid();
        JCSystem.commitTransaction();
        return true;
    }
    
    public void process(APDU apdu) throws ISOException
        //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, ?buffer_) &*& array_slice(buffer_, 0, buffer_.length, _);
        //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer_) &*& array_slice(buffer_, 0, buffer_.length, _);
    {
        byte[] buffer = apdu.getBuffer();
        // .. process the incoming data and reply
        if (buffer[ISO7816.OFFSET_CLA] == (byte)0) {
            switch (buffer[ISO7816.OFFSET_INS]) {
                case 0xA4: // ISO7816.INS_SELECT
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
