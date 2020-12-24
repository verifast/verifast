package newjticket;


import newepurse.IEPurseServicesDebit;

import javacard.framework.*;

public final class NewJTicketApplet extends Applet {

    /*** Constants ***/
    
    public static final byte JTICKET_CLA = ISO7816.CLA_ISO7816;

    public static final byte GET_COUNTER_INS = 0x01;
    public static final byte USE_TICKET_INS = 0x02;
    public static final byte BUY_TICKETS_INS = 0x03;
    public static final byte SET_EPURSE_AID_INS = 0x04;

    public static final short SW_NOT_ENOUGH_TICKETS = 0x42;
    public static final short SW_TOO_MANY_TICKETS = 0x43;
    public static final short SW_INVALID_AID = 0x44;
    public static final short SW_EPURSE_SERVICE_ERROR = 0x45;


    /*** Instance variables ***/
    
    private byte counter;
    private byte[] workingBuffer;
    private AID epurseAID;
    
    /*@
    
    predicate valid() =
        counter |-> ?c &*& 0 <= c &*&
        workingBuffer |-> ?b &*& is_transient_byte_array(b) == true &*& b.length == 16 &*&
        epurseAID |-> ?aid;
    
    @*/


    /*** Constructor ***/

    public NewJTicketApplet()
        //@ requires system();
        //@ ensures valid() &*& system();
    {
        counter = 0;
        workingBuffer = JCSystem.makeTransientByteArray((short) 16, JCSystem.CLEAR_ON_DESELECT);
    }
    

    /*** Methods ***/
        
    /**
     * Invoked by the Card Manager to install the JTicket applet.
     *
     * @param bArray - the array containing installation parameters
     * @param sOffset - the starting offset in bArray
     * @param bLength - the length in bytes of the parameter data in bArray
     */    

    public static void install(byte[] bArray, short sOffset, byte bLength)
        //@ requires array_slice(bArray, sOffset, sOffset + bLength, _) &*& system();
        //@ ensures true;
    {
        new NewJTicketApplet().register(bArray, sOffset, bLength);
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
        byte[] apduBuffer = apdu.getBuffer();
        // APDU header processing
        // CLA checking
        if (apduBuffer[ISO7816.OFFSET_CLA] != JTICKET_CLA)
            ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
        // P1 and P2 checking
        if (apduBuffer[ISO7816.OFFSET_P1] != 0 || apduBuffer[ISO7816.OFFSET_P2] != 0)
            ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
        // INS checking and dispatching
        switch (apduBuffer[ISO7816.OFFSET_INS]) {
        case GET_COUNTER_INS :
            getCounter(apdu);
            break;
        case USE_TICKET_INS :
            useTicket(apdu);
            break;
        case BUY_TICKETS_INS :
            buyTickets(apdu);
            break;
        case SET_EPURSE_AID_INS :
            setEPurseAID(apdu);
            break;
        default :
            ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }

    private void getCounter(APDU apdu)
        //@ requires [1/2]valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] apduBuffer = apdu.getBuffer();
        // LC checking
        if (apduBuffer[ISO7816.OFFSET_LC] != 0)
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
        apduBuffer[ISO7816.OFFSET_CDATA] = counter;
        apdu.setOutgoingAndSend(ISO7816.OFFSET_CDATA, (short) 1);
    }

    private void useTicket(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] apduBuffer = apdu.getBuffer();
        // LC checking
        if (apduBuffer[ISO7816.OFFSET_LC] != 0)
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
        // counter checking
        if (counter == 0)
            ISOException.throwIt(SW_NOT_ENOUGH_TICKETS);
        // counter update
        JCSystem.beginTransaction(); // Added for VeriFast
        counter--;
        JCSystem.commitTransaction(); // Added for VeriFast
    }

    private void buyTickets(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] apduBuffer = apdu.getBuffer();
        // LC checking
        if (apduBuffer[ISO7816.OFFSET_LC] != 3)
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
        // DATA processing and checking
        apdu.setIncomingAndReceive();
        byte nbOfTickets = apduBuffer[ISO7816.OFFSET_CDATA];
	//@ open valid();
	//@ transient_byte_arrays_mem(workingBuffer);
	//@ assert transient_byte_arrays(?as);
	//@ foreachp_remove(workingBuffer, as);
	//@ open transient_byte_array(workingBuffer);
        Util.arrayCopy(apduBuffer, (short) (ISO7816.OFFSET_CDATA + 1), 
                       workingBuffer, (short) 0, (short) 2);
        short amount = Util.getShort(workingBuffer, (short) 0);
        //@ close transient_byte_array(workingBuffer);
        //@ foreachp_unremove(workingBuffer, as);
        // EPurse Service call
        JCSystem.beginTransaction(); // Added for VeriFast
        IEPurseServicesDebit epurseService = 
            (IEPurseServicesDebit) JCSystem.getAppletShareableInterfaceObject(epurseAID, (byte) 0);
        if (epurseService == null)
            ISOException.throwIt(SW_EPURSE_SERVICE_ERROR);
        //@ Shareable epurseServiceSIO = epurseService;
        //@ assert epurseServiceSIO.Shareable(?epurseApplet);
        //@ mem_registered_applets_is(this);
        //@ assert registered_applets(?as1);
        //@ foreachp_unremove<Applet>(this, as1);
        //@ set_current_applet(epurseApplet);
        //@ foreachp_remove(epurseApplet, as1);
        epurseService.debit(amount);
        //@ is_registered_applets_mem(this);
        //@ assert registered_applets(?as2);
        //@ foreachp_unremove(epurseApplet, as2);
        //@ set_current_applet(this);
        //@ foreachp_remove<Applet>(this, as2);
        // counter update
        if (nbOfTickets <= 0 || (short) (nbOfTickets + counter) > 127)
            ISOException.throwIt(SW_TOO_MANY_TICKETS);
        counter += nbOfTickets;
        JCSystem.commitTransaction(); // Added for VeriFast
    }

    private void setEPurseAID(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]valid() &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
        //@ ensures current_applet(this) &*& [1/2]valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] apduBuffer = apdu.getBuffer();
        // LC checking
        byte lc = apduBuffer[ISO7816.OFFSET_LC];
        if (lc < 6 || lc > 17)
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
        apdu.setIncomingAndReceive();
        byte aidLength = apduBuffer[ISO7816.OFFSET_CDATA];
        if (lc != aidLength + 1)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);
	//@ open valid();
	//@ transient_byte_arrays_mem(workingBuffer);
	//@ assert transient_byte_arrays(?as);
	//@ foreachp_remove(workingBuffer, as);
	//@ open transient_byte_array(workingBuffer);
        Util.arrayCopy(apduBuffer, (short) (ISO7816.OFFSET_CDATA + 1), 
                       workingBuffer, (short) 0, aidLength);
        AID aid = JCSystem.lookupAID(workingBuffer, (short) 0, aidLength);
        //@ close transient_byte_array(workingBuffer);
        //@ foreachp_unremove(workingBuffer, as);
        if (aid == null)
            ISOException.throwIt(SW_INVALID_AID);
        JCSystem.beginTransaction(); // Added for VeriFast
        epurseAID = aid;
        JCSystem.commitTransaction(); // Added for VeriFast
    }

}
