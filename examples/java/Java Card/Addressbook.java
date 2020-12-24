// Note: on this program, VeriFast/Redux is 10x faster than VeriFast/Z3. To use Redux:
//    vfide -prover redux Addressbook.java
//    verifast -c -prover redux Addressbook.java

package Addressbook;

import javacard.framework.*;

//@ predicate filter_index(short element) = 0 <= element &*& element < 20;
//@ predicate groupnbs_element(byte info, byte element; byte value) = 0 <= element &*& element <= 20 &*& value == element;

public final class Addressbook extends Applet {

    //CLA byte
    private static final byte Store_CLA = (byte) 0xB0;

    //Instruction (ins) bytes
    private static final byte ADD = (byte) 0x10;
    private static final byte DELETE = (byte) 0x20;
    private static final byte SEARCH = (byte) 0x30;
    private static final byte ADDGROUP = (byte) 0x40;
    private static final byte DELETEGROUP = (byte) 0x50;
    private static final byte ADDCONTACTTOGROUP = (byte) 0x41;
    private static final byte REMOVECONTACTFROMGROUP = (byte) 0x42;
    private static final byte SEARCHINGROUP = (byte) 0x43;
    private static final byte FILTERCONTACTS = (byte) 0x61;

    //Error bytes
    private static final byte SW_ADDRESSBOOK_FULL = (byte) 0x5300;
    private static final byte SW_PERSON_NOT_FOUND = (byte) 0x2100;
    private static final byte SW_GROUP_NOT_FOUND = (byte) 0x6100;
    private static final byte SW_GROUPBOOK_FULL = (byte) 0x6200;
    private static final byte SW_GROUP_FULL = (byte) 0x6300;
    private static final byte SW_NO_PERSON_FOUND = (byte) 0x4000;

    //Number of bytes for nr,name,record,groupname and groupnumbers
    private static final short NR_LENGTH = 5;
    private static final short NAME_LENGTH = 15;
    private static final short RECORD_LENGTH = 20;
    private static final short GROUPNAME_LENGTH = 10;
    private static final short GROUPNUMBERS_LENGTH = 10;

    //Array Declarations
    private static byte[] zeros;
    private static byte[] phoneNbs;
    private static short[] emptyPhoneNbs;//Marks empty places in the phonebook(PhoneNbs)
    private static byte[] groupnames;
    private static byte[] groupnbs;//Contains for each group the contactnbs (index of contact in phoneNbs) that belong to the group
    private static short[] emptyGroups;//Marks empty groups in groupnames.
    private static byte[] filteredNames;

     /*@
    predicate valid() = emptyPhoneNbs |-> ?e_array &*& e_array != null &*& array_slice(e_array,0,e_array.length,_) &*& e_array.length == 20
    			&*& phoneNbs |-> ?t_array &*& t_array != null &*& array_slice(t_array,0,t_array.length,_) &*& t_array.length == 400
    			&*& zeros |-> ?z_array &*& z_array != null &*& array_slice(z_array,0,z_array.length,_) &*& z_array.length == 20
    			&*& groupnames |-> ?g_array &*& g_array != null &*& array_slice(g_array,0,g_array.length,_) &*& g_array.length == 100
      	                &*& groupnbs |-> ?nb_array &*& nb_array != null &*& array_slice_deep(nb_array, 0, nb_array.length, groupnbs_element, 0, _,_) &*& nb_array.length == 100
    			&*& emptyGroups |-> ?ge_array &*& ge_array != null &*& array_slice(ge_array,0,ge_array.length,_) &*& ge_array.length == 10
    			&*& filteredNames |-> ?f_array &*& f_array != null &*& array_slice(f_array,0,f_array.length,_) &*& f_array.length == 400;
    @*/ 

    public static void install(byte[] bArray, short bOffset, byte bLength)
    //@ requires class_init_token(Addressbook.class) &*& system();
    //@ ensures true;
    {
        Addressbook addressbook = new Addressbook();
        addressbook.register();
    }

    protected Addressbook()
    //@ requires class_init_token(Addressbook.class);
    //@ ensures valid();
    {
        //@ init_class();
        phoneNbs = new byte[400];
        emptyPhoneNbs = new short[20];
        zeros = new byte[20];
        groupnames = new byte[100];
        groupnbs = new byte[100];
        emptyGroups = new short[10];
        filteredNames = new byte[400];

        //Initialize the groupnbs array
        for(short i =0; i< 100; i++)
        //@ invariant 0 <= i &*& groupnbs |-> ?gn_array &*& array_slice_deep(gn_array,0,i,groupnbs_element,0,?ielems,_) &*& array_slice(gn_array,i,gn_array.length,?elems) &*& gn_array.length == 100;
        {
        	groupnbs[i] = (byte)0;
        	//@ close groupnbs_element(0,0,0);
        	//@ array_slice_deep_close(gn_array,i,groupnbs_element,0);

        }
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

        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
          ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);

        switch(abuffer[ISO7816.OFFSET_INS]){
            case ADD: add(apdu);return;
            case DELETE: delete(apdu);return;
            case SEARCH: search(apdu);return;
            case ADDGROUP: addGroup(apdu);return;
            case DELETEGROUP: deleteGroup(apdu);return;
            case ADDCONTACTTOGROUP: addContactToGroup(apdu);return;
            case REMOVECONTACTFROMGROUP: removeContactFromGroup(apdu);return;
            case SEARCHINGROUP: searchInGroup(apdu);return;
            case FILTERCONTACTS: filterContacts(apdu);return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }

    private void add(APDU apdu)
    //@requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != RECORD_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyPhoneNbs.length;
        //@close [1/2]valid();

        boolean added = false;

        //Search empty space in phoneNbs by inspecting emptyPhoneNbs
        //if empty space found, store contact in that space
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            short item = emptyPhoneNbs[i];
            //@close [1/2]valid();

            if(item == 0 && added==false){
                JCSystem.beginTransaction();
                added = true;
                //@open valid();
                //Mark space used
                emptyPhoneNbs[i] = 1;
                //Copy contactdata in empty space phoneNbs
                Util.arrayCopy(abuffer,(short)ISO7816.OFFSET_CDATA,phoneNbs,(short)(i * RECORD_LENGTH),(short) RECORD_LENGTH);
                //@close valid();
                JCSystem.commitTransaction();
            }
        }

        if(!added)
            ISOException.throwIt(SW_ADDRESSBOOK_FULL);
    }

    private void delete(APDU apdu)
    //@requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyPhoneNbs.length;
        //@close [1/2]valid();

        //Search each record of phoneNbs
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            short item = emptyPhoneNbs[i];
            //@close [1/2]valid();

            //If there exists a record in phoneNbs on index
            if(item == 1){
                //@ open [1/2]valid();
                //Match names of record in phoneNbs and in incoming apdu
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
                //@ close [1/2]valid();

                if(equal == 0){
                    JCSystem.beginTransaction();
                    //@ open valid();
                    //Set recordplace on empty
                    emptyPhoneNbs[i] = 0;
                    //Overwrite record with zeros
                    Util.arrayCopy(zeros,(short)0,phoneNbs,(short)(i * RECORD_LENGTH),(short) RECORD_LENGTH);
                    //@ close valid();
                    JCSystem.commitTransaction();
                }
            }
        }
    }

    private void search(APDU apdu)
    //@ requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyPhoneNbs.length;
        //@close [1/2]valid();
        boolean found = false;
        //Search each record of phoneNbs
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            short item = emptyPhoneNbs[i];
            //@close [1/2]valid();
            //If there exists a record on index & record not found
            if(item == 1 && found == false){
            	//@ open [1/2]valid();
                //If names of the record in phoneNbs and incoming apdu match
                if(Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH) == 0){
                    found = true;
                    apdu.setOutgoing();
                    apdu.setOutgoingLength(NR_LENGTH);
                    apdu.sendBytesLong(phoneNbs, (short)((i * RECORD_LENGTH)+NAME_LENGTH), NR_LENGTH);
                }
                //@ close [1/2]valid();
            }
        }
        
        if(found == false){
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
        }
    }

    private void addGroup (APDU apdu)
    //@ requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]this.valid();
    //@ ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]this.valid();
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyGroups.length;
        //@close [1/2]valid();

        boolean added = false;
        //Search empty space in groupnames
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& 0 <= i;
        {
            //@ open [1/2]valid();
            short item = emptyGroups[i];
            //@close [1/2]valid();
            //If groupname space empty and groupname not stored
            if(item == 0 && added==false){
                JCSystem.beginTransaction();
                added = true;

  		//@open valid();
                //Mark space used
                emptyGroups[i] = 1;
                //Copy groupname date in empty space groupnames
                Util.arrayCopy(abuffer,(short)ISO7816.OFFSET_CDATA,groupnames,(short)(i * GROUPNAME_LENGTH),(short) GROUPNAME_LENGTH);
                //@close valid();
                JCSystem.commitTransaction();
            }
        }
       
        if(added == false){
            ISOException.throwIt(SW_GROUPBOOK_FULL);
        }
    }

    private void addContactToGroup (APDU apdu)
    //@ requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyPhoneNbs.length;
        //@close [1/2]valid();

        boolean found = false;
        byte contactnb = 0;
        //Search each record in phoneNbs
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0 &*& 0 <= contactnb &*& contactnb <= 20;
        {
            //@ open [1/2]valid();
            //Match contact name from phoneNbs and incoming apdu
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
            //@ close [1/2]valid();
            //If contact not yet found & record name equals
            if(found==false && equal == 0 ){
                found = true;
                //Store index of contactrecord
                contactnb = (byte)(short)(i+1);
            }
        }

        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);

        //@open [1/2]valid();
        short g_length = (short) emptyGroups.length;
        //@close [1/2]valid();

        boolean g_found = false;
        boolean added = false;

        //Search for group in groupnames
        for(short i=0;i<g_length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            //Match groupname of groupnames and incoming apdu
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
            //@ close [1/2]valid();
            //If group not found & groupname equals
            if(g_found==false && equal == 0 ){
                g_found = true;

                //begin and end of nbs in groupnbs for searched group
                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                //Search empty contactnb-space in space of groupname in groupnbs
                for(short a=begin;a<end;a++)
                //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& a >= 0;
                {
                    //@ open [1/2]valid();
                    byte openplace = groupnbs[a];
                    //@ close groupnbs_element(0,openplace,openplace);
                    //@ array_slice_deep_close(groupnbs,a,groupnbs_element,0);
                    //@ close [1/2]valid();
                    //If contact not yet added & empty space found
                    if(added == false && openplace == 0){
                        JCSystem.beginTransaction();
                        added = true;
                        //@ open valid();
                        //Write contactnb in empty space
                        groupnbs[a] = contactnb;
                        //@ close groupnbs_element(0,contactnb,contactnb);
                        //@ close valid();
                        JCSystem.commitTransaction();
                    }
                }
            }
        }

        if(g_found == false)
            ISOException.throwIt(SW_GROUP_NOT_FOUND);
        if(added == false)
            ISOException.throwIt(SW_GROUP_FULL);
    }

    private void removeContactFromGroup (APDU apdu)
    //@ requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyPhoneNbs.length;
        //@close [1/2]valid();

        boolean found = false;
        byte contactnb = 0;
        //Search each record in phoneNbs
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            //Match contact name in phoneNbs and incoming apdu
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
            //@ close [1/2]valid();
            //If record not yet found & contact name equals
            if(found==false && equal == 0 ){
                found = true;
                //Store index nb of contact in phoneNbs into contactnb
                contactnb = (byte)(short)(i+1);
            }
        }

        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);

        //@open [1/2]valid();
        short g_length = (short) emptyGroups.length;
        //@close [1/2]valid();

        boolean g_found = false;

        //Search for group in groupnames
        for(short i=0;i<g_length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            //Match groupname in groupnames and incoming apdu
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
            //@ close [1/2]valid();
            //If group not yet found & groupname equals
            if(g_found==false && equal == 0 ){
                g_found = true;

                //begin and end of nbs in groupnbs of searched group
                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                //Search contactnb in space of groupname in groupnbs
                for(short a=begin;a<end;a++)
                //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& a >= 0;
                {
                    //@ open [1/2]valid();
                    byte contactequal = groupnbs[a];
                    //@ close groupnbs_element(0,contactequal,contactequal);
                    //@ array_slice_deep_close(groupnbs,a,groupnbs_element,0);
                    //@ close [1/2]valid();
                    //If calculated contactnb en contactnb in groupnbs match
                    if(contactequal == contactnb){
                        JCSystem.beginTransaction();
                        //@ open valid();
                        //Erase contactnb
                        groupnbs[a] = (byte)0;
                        //@ close groupnbs_element(0,0,0);
                        //@ array_slice_deep_close(groupnbs,a,groupnbs_element,0);
                        //@ close valid();
                        JCSystem.commitTransaction();
                    }
                }
            }
        }

        if(g_found == false)
            ISOException.throwIt(SW_GROUP_NOT_FOUND);
    }

    private void deleteGroup (APDU apdu)
    //@ requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
         byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

	//@open [1/2]valid();
        short length = (short) emptyGroups.length;
        //@close [1/2]valid();

        //Search for group in groupnames
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& 0 <= i;
        {
            //@ open [1/2]valid();
            short item = emptyGroups[i];
            //@close [1/2]valid();
            //If groupname stored on index
            if(item == 1){
                //@ open [1/2]valid();
                //Match groupname in groupnames and incoming apdu
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
                //@ close [1/2]valid();
                //If groupname matches
                if(equal == 0){
                    JCSystem.beginTransaction();
                    //@ open valid();
                    //Mark space in groupnames empty
                    emptyGroups[i] = 0;
                    //Erase groupname in groupnames
                    Util.arrayCopy(zeros,(short)0,groupnames,(short)(i * GROUPNAME_LENGTH),(short) GROUPNAME_LENGTH);
                    //@ close valid();
                    short begin = (short)(i * GROUPNUMBERS_LENGTH);
                    short end = (short)(begin + GROUPNUMBERS_LENGTH);
                    //Erase contactnbs in contactnb-space in space of groupname in groupnbs
                    for(short a = begin; a < end; a++)
                    //@ invariant begin <= a &*& valid();
                    {
                        //@ open valid();
                        groupnbs[a] = (byte)0;
                        //@ close groupnbs_element(0,0,0);
                        //@ array_slice_deep_close(groupnbs,a,groupnbs_element,0);
                        //@ close valid();
                    }
                    JCSystem.commitTransaction();
                }
            }
        }
    }

    private void searchInGroup (APDU apdu)
    //@ requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();

        if(abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH + NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyGroups.length;
        //@close [1/2]valid();

        boolean found = false;
        //Search group in groupnames
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            short item = emptyGroups[i];
            //@close [1/2]valid();
            //If index in groupnames not empty
            if(item == 1){
                //@ open [1/2]valid();
                //Match groupname in groupnames and incoming apdu
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
                //@ close [1/2]valid();
                //If groupname matches
                if(equal == 0){

                    //begin and end of nbs in groupnbs of searched group
                    short begin = (short)(i * GROUPNUMBERS_LENGTH);
                    short end = (short)(begin + GROUPNUMBERS_LENGTH);
                    //Search contact in space of groupname in groupnbs
                    for(short a=begin;a<end;a++)
                    //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& a >= 0;
                    {
                        //@ open [1/2]valid();
                        byte contactnb = groupnbs[a];
                        //@ close groupnbs_element(0,contactnb,contactnb);
                        //@ array_slice_deep_close(groupnbs,a,groupnbs_element,0);
                        //@ close [1/2]valid();
                        //If contactnb on index of groupnbs contains contactnb en contact not found
                        if(contactnb > (byte)0 && found == false){
                            //@ open [1/2]valid();
                            //Match contactname in phoneNbs and incoming apdu
                            //contact in phoneNbs can be found by contactnb (contactnb = index contact in phoneNbs)
                            short same_name = (short)Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + GROUPNAME_LENGTH), phoneNbs, (short)((contactnb-1) * RECORD_LENGTH), NAME_LENGTH);
                            //@ close [1/2]valid();
                            //If contactname matches send contact phone nb
                            if(same_name == 0){
                                found = true;
                                apdu.setOutgoing();
                                apdu.setOutgoingLength(NR_LENGTH);
                                //@ open [1/2]valid();
                                apdu.sendBytesLong(phoneNbs, (short)(((contactnb-1) * RECORD_LENGTH) + NAME_LENGTH), NR_LENGTH);
                                //@ close [1/2]valid();
                            }
                        }
                    }
                }
            }
        }
        if(found == false)
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
    }

    private void filterContacts(APDU apdu)
    //@ requires APDU(apdu,?buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    //@ ensures APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid();
    {
        byte[] abuffer = apdu.getBuffer();

        short filterlength = (short)(abuffer[ISO7816.OFFSET_LC] & 0xff);
        if(filterlength > NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@open [1/2]valid();
        short length = (short) emptyPhoneNbs.length;
        //@close [1/2]valid();
        boolean found = false;

        //index of filteredNames
        short index = (short)0;
        //@ close filter_index(index);
        //Loop to fetch all filtered names
        //match every record in phoneNbs
        for(short i=0;i<length;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0 &*& filter_index(index);
        {
            //@ open [1/2]valid();
            short item = emptyPhoneNbs[i];
            //@close [1/2]valid();
            //If phoneNbs record not empty
            if(item == 1){
            	//@ open [1/2]valid();
                //Match contactname with filter on filterlength
            	short compare = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), filterlength);
            	//@ close [1/2]valid();
                //If filter matches
                if(compare == 0){
                    found = true;
                    JCSystem.beginTransaction();
                    //@ open valid();
                    //@ open filter_index(index);
                    if(i > 0 && index < 19){
                    	index++;
                    }
                    //Store contact in filteredNames
                    Util.arrayCopy(phoneNbs, (short)(i*RECORD_LENGTH), filteredNames,(short)(index * NAME_LENGTH), NAME_LENGTH);
                    //@ close filter_index(index);
                    //@ close valid();
                    JCSystem.commitTransaction();
                }
            }
        }

        if(found == false){
            ISOException.throwIt(SW_NO_PERSON_FOUND);
        }

        apdu.setOutgoing();
        //@ open [1/2]filter_index(index);
        apdu.setOutgoingLength((short)((index + 1)*NAME_LENGTH));
        //@ close [1/2]filter_index(index);
        //Loop for sending filtered names
        for(short i=0;i<=index;i++)
        //@ invariant APDU(apdu,buffer) &*& array_slice(buffer,0,buffer.length,_) &*& current_applet(this) &*& [1/2]valid() &*& i >= 0;
        {
            //@ open [1/2]valid();
            apdu.sendBytesLong(filteredNames, (short)(i*NAME_LENGTH), NAME_LENGTH);
            //@ close [1/2]valid();
        }

    }
}