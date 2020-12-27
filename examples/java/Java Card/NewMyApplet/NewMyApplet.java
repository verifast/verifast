// Note: VeriFast/Redux is much faster than VeriFast/Z3 on this applet. Use vfide -prover redux MyApplet.java or verifast -c -allow_assume -prover redux MyApplet.java

// The assume statements in this file represent assumptions that the applet makes about the input.
// What we are proving here is that in any execution of the applet where the input satisfies these assumptions, the applet does not dereference null pointers,
// access arrays with indices that are out of bounds, divide by zero, perform arithmetic overflow, violate API contracts, or violate the assertions specified in the code.

package newmypackage;

import org.globalplatform.GPSystem;

import be.fedict.neweidapplet.INewEidPoints;

import newepurse.IEPurseServicesCredit;
import newepurse.IEPurseServicesDebit;

import javacard.framework.*;

/*@

lemma_auto void length_append_auto<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    length_append(xs, ys);
}

predicate length_value_record(list<byte> values, int start; int end) =
    start < length(values) &*&
    0 <= nth(start, values) &*&
    start + 1 + nth(start, values) <= length(values) &*&
    end == start + 1 + nth(start, values);

predicate element(list<byte> values, int offset; byte value) =
    offset < length(values) &*&
    value == nth(offset, values);

predicate optional_data_records(byte[] array, int start, int count;) =
    count == 0 ?
        true
    :
        0 < count &*&
        array[start..start + 2] |-> _ &*&
        array[start + 2] |-> ?length &*& 0 <= length &*& length <= NewMyApplet.MAX_LEN_OPTIONAL_DATA &*&
        array[start + 3..start + 3 + NewMyApplet.MAX_LEN_OPTIONAL_DATA] |-> _ &*&
        optional_data_records(array, start + 3 + NewMyApplet.MAX_LEN_OPTIONAL_DATA, count - 1);

lemma void optional_data_records_split(byte[] array, int start, int offset)
    requires [?f]optional_data_records(array, start, ?count) &*& 0 <= offset &*& offset <= count;
    ensures [f]optional_data_records(array, start, offset) &*& [f]optional_data_records(array, start + offset * 13, count - offset);
{
    if (offset == 0) {
        close [f]optional_data_records(array, start, 0);
    } else {
        open optional_data_records(array, start, count);
        optional_data_records_split(array, start + 13, offset - 1);
        close [f]optional_data_records(array, start, offset);
    }
}

lemma void optional_data_records_merge(byte[] array, int start)
    requires [?f]optional_data_records(array, start, ?count1) &*& [f]optional_data_records(array, start + count1 * 13, ?count2);
    ensures [f]optional_data_records(array, start, count1 + count2) &*& 0 <= count1 + count2;
{
    open optional_data_records(array, start, count1);
    if (count1 == 0) {
        open optional_data_records(array, start, count2);
        close [f]optional_data_records(array, start, count2);
    } else {
        optional_data_records_merge(array, start + 13);
        close [f]optional_data_records(array, start, count1 + count2);
    }
}

predicate record(int maxSizeRecord, byte[] record; unit info) =
  record != null &*&
  true == ((record).length == maxSizeRecord + NewMyApplet.LEN_RECORD_LEN_BYTE) &*&
  array_element(record, 0, ?recordLength) &*& 0 <= recordLength &*& 0 + recordLength <= maxSizeRecord &*&
  array_slice(record, 1, 6, _) &*&
  array_element(record, 6, ?adfLength) &*& 0 <= adfLength &*& 6 + adfLength <= maxSizeRecord &*&
  array_slice(record, 7, 1 + maxSizeRecord, _) &*&
  info == unit;

predicate my_record(int maxSizeRecord, Object record; unit info) =
  record(maxSizeRecord, ^record, unit) &*& info == unit;

predicate MyApplet_(NewMyApplet applet; char nbRecords, byte maxSizeRecord) =
  applet.NewEPurseAID |-> ?newEPurseAid &*& newEPurseAid[..] |-> _ &*& newEPurseAid.length == 6 &*&
  applet.NewEidAID |-> ?newEidAid &*& newEidAid[..] |-> _ &*& newEidAid.length == 9 &*&
  applet.NewEidPointsObject |-> _ &*&
  applet.NewEPurseDebitObject |-> _ &*&
  applet.NewEPurseCreditObject |-> _ &*&
  applet.NewMyAppletPointsObject |-> ?pointsObject &*& [_]pointsObject.applet |-> applet &*&
  NewMyApplet_Points(_) &*&
  NewMyApplet_bya_FCI(?fci) &*& fci[..] |-> _ &*& fci.length == 23 &*&
  applet.by_NbRecords |-> nbRecords &*& 0 <= nbRecords &*&
  applet.by_MaxNbRecord |-> ?maxNbRecord &*& nbRecords <= maxNbRecord &*&
  applet.by_MaxSizeRecord |-> maxSizeRecord &*& maxSizeRecord >= NewMyApplet.OFF_DATA_IN_RECORD + 5 &*&
  applet.bya_OptionalData |-> ?optionalData &*& optionalData != null &*& optionalData.length == NewMyApplet.SIZE_OPTIONAL_DATA_BUFFER &*&
  optional_data_records(optionalData, 0, 3) &*&
  applet.o_Records |-> ?records &*& records != null &*& records.length == maxNbRecord &*&
  array_slice_deep(records, 0, nbRecords, my_record, maxSizeRecord, _, _) &*&
  records[nbRecords..maxNbRecord] |-> ?elems &*& all_eq(elems, null) == true;

@*/

public final class NewMyApplet extends Applet {

  static final boolean B_MODE_DEBUG = false;

  static final byte DEF_MAX_ENTRIES = (byte) 5;
  static final byte DEF_MAX_ENTRY_SIZE = (byte) 50;

  static final byte  LEN_RECORD_LEN_BYTE = (byte) 01;
  static final short OFF_DATA_IN_RECORD = (short) 01;

  static final byte ADF_LEN_OFFSET = (byte) 10;
  static final byte ADF_OFFSET = (byte) 11;

  static final short MAX_LEN_OPTIONAL_DATA = (short) 10;
  static final short MAX_LEN_OPTIONAL_DATA_AND_HEADER = (short)(MAX_LEN_OPTIONAL_DATA + 3);
  static final short SIZE_OPTIONAL_DATA_BUFFER = (short)(3 * MAX_LEN_OPTIONAL_DATA_AND_HEADER);
  static final short TAG_LANGUAGE_PREFERENCE = (short) 0x1234 ;
  static final short TAG_ISSUER_CODE_TABLE_INDEX = (short) 0x1235 ;
  static final short TAG_FCI_ISSUER_DISCRETIONARY_DATA = (short) 0x1236 ;

  byte by_NbRecords;
  byte by_MaxNbRecord;

  byte by_MaxSizeRecord;

  byte[] bya_OptionalData;

  Object[] o_Records;

  static final byte bya_FCI[] =
  {
    (byte)0x12, (byte)21,
    (byte)0x12, (byte)14,
    (byte)'X',  (byte)'X', (byte)'X', (byte)'X', (byte)'X',
    (byte)'X',  (byte)'X', (byte)'X', (byte)'X',
    (byte)'X',  (byte)'X', (byte)'X', (byte)'X', (byte)'X',
    (byte)0x12, (byte)3,
    (byte)0x12, (byte)1,  (byte)1
  };

  	public static final byte INS_Debit = 0x01;
	public static final byte INS_Eid_Points = 0x03;
	private byte[] NewEPurseAID = {0x01,0x02,0x03,0x04,0x05,0x00};
	private IEPurseServicesDebit NewEPurseDebitObject;
	private IEPurseServicesCredit NewEPurseCreditObject;
	private byte[] NewEidAID = {0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x00};
	private INewEidPoints NewEidPointsObject;
	public static byte Points = 5;
	NewMyAppletPoints NewMyAppletPointsObject;

    //@ predicate valid() = MyApplet_(this, _, _);

  private NewMyApplet(byte[] byaBuffer, short shOffset, byte byLength, byte byMaxNbRecord, byte byMaxSizeRecord)
    //@ requires system() &*& 0 <= byMaxNbRecord &*& 6 <= byMaxSizeRecord &*& Points |-> _ &*& bya_FCI |-> ?fci &*& array_slice(fci, 0, 23, _) &*& fci.length == 23 &*& array_slice(byaBuffer, shOffset, shOffset + byLength, _);
    //@ ensures true;
  {
	NewMyAppletPointsObject = new NewMyAppletPoints();
	//@ NewMyAppletPointsObject.applet = this;
		
    by_MaxNbRecord   = byMaxNbRecord;
    by_MaxSizeRecord = byMaxSizeRecord;

    bya_OptionalData = new byte[SIZE_OPTIONAL_DATA_BUFFER];
    //@ close optional_data_records(bya_OptionalData, 3 * MAX_LEN_OPTIONAL_DATA_AND_HEADER, 0);
    //@ close optional_data_records(bya_OptionalData, 2 * MAX_LEN_OPTIONAL_DATA_AND_HEADER, 1);
    //@ close optional_data_records(bya_OptionalData, 1 * MAX_LEN_OPTIONAL_DATA_AND_HEADER, 2);
    //@ close optional_data_records(bya_OptionalData, 0 * MAX_LEN_OPTIONAL_DATA_AND_HEADER, 3);

    o_Records = new Object[by_MaxNbRecord];

    //@ close valid();
    if( byLength == 0 )
    {
      register();
    }
    else
    {
      register(byaBuffer, shOffset, byLength);
    }
  }

  public static void install(byte[] byaBuffer, short shOffset, byte byLength) throws ISOException /*@ ensures true; @*/
    /*@
    requires
      system() &*& class_init_token(NewMyApplet.class) &*&
      byaBuffer != null &*&
      shOffset >= 0 &*&
      array_slice(byaBuffer, shOffset, shOffset + byLength, ?values) &*&
      length_value_record(values, 0, ?privilegesStart) &*&
      length_value_record(values, privilegesStart, ?paramsStart) &*&
      element(values, paramsStart + 1, ?paramsLength) &*&
      element(values, paramsStart + 2, ?maxNbRecord) &*& maxNbRecord >= 0 &*&
      element(values, paramsStart + 3, ?maxSizeRecord) &*& maxSizeRecord >= 6 &*&
      shOffset + paramsStart + 3 <= 32767;
    @*/
    //@ ensures true;
  {
    //@ init_class();
    short shIndex = shOffset;
    byte byMaxNbRecord   = DEF_MAX_ENTRIES ;
    byte byMaxSizeRecord = DEF_MAX_ENTRY_SIZE;

    //@ open length_value_record(values, 0, privilegesStart);
    //@ open length_value_record(values, privilegesStart, _);
    shIndex += (byaBuffer[shIndex]+1);
    shIndex += (byaBuffer[shIndex]+1);

    ++shIndex;
    // BUG: byte byOffRecParam = (byte)shIndex ; The Java Card spec does not guarantee that the offset fits in a byte.
    short byOffRecParam = shIndex ;
    //@ open element(values, shIndex - shOffset, _);
    //@ open element(values, shIndex + 1 - shOffset, _);
    //@ open element(values, shIndex + 2 - shOffset, _);
    byte byLenRecParam = byaBuffer[shIndex] ;
    //
    if (byLenRecParam != 0)
    {
      ++byOffRecParam;
      byMaxNbRecord    = (byaBuffer[byOffRecParam] != 0) ? byaBuffer[byOffRecParam] : DEF_MAX_ENTRIES;
      ++byOffRecParam;
      byMaxSizeRecord  = (byaBuffer[byOffRecParam] != 0) ? byaBuffer[byOffRecParam] : DEF_MAX_ENTRY_SIZE;
    }

    new NewMyApplet(byaBuffer, (short)(shOffset+1), byaBuffer[shOffset], byMaxNbRecord, byMaxSizeRecord);
  }

  public void process(APDU oApdu)
    /*@
    requires
      current_applet(this) &*&
      [1/2]valid() &*&
      oApdu != null &*&
      APDU(oApdu, ?buffer) &*&
      array_slice(buffer, 0, buffer.length, _);
    @*/
    /*@
    ensures
      current_applet(this) &*&
      [1/2]valid() &*&
      oApdu != null &*&
      APDU(oApdu, buffer) &*&
      array_slice(buffer, 0, buffer.length, _);
    @*/
  {
    byte[] byaApdu = oApdu.getBuffer();

    switch(sh(byaApdu[ISO7816.OFFSET_CLA]))
    {
    case 0x00:
      switch(sh(byaApdu[ISO7816.OFFSET_INS]))
      {
      case 0xa4:
        processSelectCmd(oApdu);
        return;
      case 0xb2:
        processReadRecord(oApdu);
        return;
      case 0xe4:
        processDeleteRecord(oApdu);
        return;
      case 0xc0:
        return;
      case 0xcb:
        if (B_MODE_DEBUG)
        {
          /*
          if(Util.getShort(byaApdu, (short)2) == (short)0x9f01)
          {
            byaApdu[4] = by_MaxNbRecord ;
            byaApdu[5] = by_MaxSizeRecord ;
            oApdu.setOutgoingAndSend((short)2, (short)4) ;
            return;
          }
          */
        }
      case INS_Debit:
			askForPayment();
			break;
      case INS_Eid_Points:
		   askForSharingPoints();
		   break;
      default:
        ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
      }
    case 0x80 :
      switch(sh(byaApdu[ISO7816.OFFSET_INS]))
      {
      case 0xda:
        processPutData(oApdu);
        return;
      case 0xe2:
        processAppendRecord(oApdu);
        return;
      case INS_Debit:
		askForPayment();
		break;
      case INS_Eid_Points:
	    askForSharingPoints();
	    break;
      default:
        ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
      }
    default:
      ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
    }
  }

  private void processSelectCmd(APDU oApdu)
    //@ requires [1/2]valid() &*& oApdu != null &*& APDU(oApdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures [1/2]valid() &*& oApdu != null &*& APDU(oApdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
  {
    if ( !selectingApplet() )
      ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
    byte[] byaApdu = checkIncomingData(oApdu, true, false);
    short shCurrentOffset = 0;
    if (sh(byaApdu[ISO7816.OFFSET_LC]) == (short)0)
      ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
    if((byaApdu[ISO7816.OFFSET_P1]) != 0x04)
      ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
    //@ open valid();
    //@ open MyApplet_(this, _, _);
    byte[] byaOptionalData = bya_OptionalData;
    shCurrentOffset = Util.arrayCopyNonAtomic( bya_FCI, shCurrentOffset, byaApdu, (short)0, (short)bya_FCI.length );
    byte k,j;
    //@ int i = 2;
    //@ optional_data_records_split(byaOptionalData, 0, i);


    for(k=26,j=28 ; k>=0 ; k-=13,j-=13)
      /*@
      invariant
          -13 <= k &*& k <= 26 &*& j == k + 2 &*& k == 13 * i &*&
          array_slice(byaApdu, 0, byaApdu.length, _) &*&
          23 <= shCurrentOffset &*&
          shCurrentOffset <= 23 + 13 * (2 - i) &*&
          k < 0 ?
              [1/2]optional_data_records(byaOptionalData, 0, 3)
          :
              [1/2]optional_data_records(byaOptionalData, 0, i) &*& [1/2]optional_data_records(byaOptionalData, k, 3 - i);
      @*/
    {
        //@ open optional_data_records(byaOptionalData, k, _);
      shCurrentOffset = Util.arrayCopyNonAtomic( byaOptionalData, k,
          byaApdu, shCurrentOffset,
          (byaOptionalData[j] != 0)? (short)(byaOptionalData[j] + 3): (short)0);
      //@ close [1/2]optional_data_records(byaOptionalData, k, 3 - i);
      //@ i--;
      /*@
      if (0 <= i) {
          optional_data_records_split(byaOptionalData, 0, i);
          open optional_data_records(byaOptionalData, k - 13, _);
          close [1/2]optional_data_records(byaOptionalData, k - 13, 3 - i);
      }
      @*/
    }
    shCurrentOffset -= /**/bya_FCI.length;
    //@ assume(bya_FCI[3] == 14);
    byaApdu[bya_FCI[3]+5] = (byte)(shCurrentOffset + 3);
    byaApdu[1] = (byte)(shCurrentOffset + 3+2 + bya_FCI[3]+2);
    oApdu.setOutgoingAndSend((short)0, (short)(sh(byaApdu[1]) + (short)2));
    //@ close [1/2]MyApplet_(this, _, _);
    //@ close [1/2]valid();
  }

  private byte[] checkIncomingData(APDU oApdu, boolean bReceive, boolean bCheckPersoState)
    //@ requires oApdu != null &*& APDU(oApdu, ?buffer_) &*& array_slice(buffer_, 0, buffer_.length, _);
    //@ ensures APDU(oApdu, buffer_) &*& array_slice(buffer_, 0, buffer_.length, _) &*& result == buffer_;
  {
    if (bCheckPersoState && GPSystem.getCardContentState() != GPSystem.SECURITY_DOMAIN_PERSONALIZED )
      ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
    if (bReceive) oApdu.setIncomingAndReceive();
    return oApdu.getBuffer();
  }

  private void processPutData(APDU oApdu)
    //@ requires current_applet(this) &*& [1/2]valid() &*& oApdu != null &*& APDU(oApdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures current_applet(this) &*& [1/2]valid() &*& oApdu != null &*& APDU(oApdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
  {
    byte[] byaApdu = checkIncomingData(oApdu, true, true); // true => personalization must have previously been done
    short shLC = sh(byaApdu[ISO7816.OFFSET_LC]) ;
    //@ open is_short_of_byte(_, _);

    if (shLC > MAX_LEN_OPTIONAL_DATA)
      ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);

    byte byIndex = getOptionalDataIndex(Util.getShort( byaApdu, ISO7816.OFFSET_P1 ));

    JCSystem.beginTransaction(); // Inserted for VeriFast
    //@ open valid();
    //@ open MyApplet_(this, _, _);
    byte[] byaOptionalData = bya_OptionalData;
    //@ optional_data_records_split(byaOptionalData, 0, byIndex);
    //@ open optional_data_records(byaOptionalData, byIndex * MAX_LEN_OPTIONAL_DATA_AND_HEADER, 3 - byIndex);
    Util.arrayCopy( byaApdu, ISO7816.OFFSET_P1,
        byaOptionalData,
        (short) (byIndex * MAX_LEN_OPTIONAL_DATA_AND_HEADER),
        (short) (shLC + (short)3));
    //@ assert byaOptionalData[byIndex * 13 + 2] |-> ?length;
    //@ assume(0 <= length && length <= NewMyApplet.MAX_LEN_OPTIONAL_DATA);
    //@ close optional_data_records(byaOptionalData, byIndex * MAX_LEN_OPTIONAL_DATA_AND_HEADER, 3 - byIndex);
    //@ optional_data_records_merge(byaOptionalData, 0);
    //@ close MyApplet_(this, _, _);
    //@ close valid();
    JCSystem.commitTransaction(); // Inserted for VeriFast
  }

  private byte getOptionalDataIndex(short tag)
    //@ requires true;
    //@ ensures 0 <= result &*& result <= 2;
  {
    switch (tag)
    {
    case TAG_FCI_ISSUER_DISCRETIONARY_DATA : return 0 ;
    case TAG_ISSUER_CODE_TABLE_INDEX : return 1;
    case TAG_LANGUAGE_PREFERENCE : return 2;
    default :
      ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
    }
    return -1; //~allow_dead_code
  }

  private void processAppendRecord(APDU oApdu)
    //@ requires current_applet(this) &*& [1/2]valid() &*& oApdu != null &*& APDU(oApdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures current_applet(this) &*& [1/2]valid() &*& oApdu != null &*& APDU(oApdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
  {
      //@ open valid();
      //@ open MyApplet_(this, _, _);
    byte[] byaApdu = checkIncomingData(oApdu, true, false);
    short shLC = sh(byaApdu[ISO7816.OFFSET_LC]) ;
    if((byaApdu[ISO7816.OFFSET_P1] != 0)
        || (byaApdu[ISO7816.OFFSET_P2]&0x07) != 0)
      ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
    if((byaApdu[ISO7816.OFFSET_P2]>>3) != 1)
      ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
    //@ open is_short_of_byte(_, _);
    if ( shLC > sh(by_MaxSizeRecord) )
      ISOException.throwIt( ISO7816.SW_FILE_FULL );
    //@ open is_short_of_byte(_, _);
    //@ byte maxSizeRecord = by_MaxSizeRecord;
    //@ assert 0 <= shLC &*& shLC <= maxSizeRecord;

    if (byaApdu[ISO7816.OFFSET_CDATA] != (byte)0x70)
      ISOException.throwIt( ISO7816.SW_CONDITIONS_NOT_SATISFIED );

    //@ assume(0 <= byaApdu[ADF_LEN_OFFSET] && byaApdu[ADF_LEN_OFFSET] <= 133 - ADF_OFFSET);
    if (JCSystem.lookupAID( byaApdu, ADF_OFFSET, byaApdu[ADF_LEN_OFFSET] )== null)
      ISOException.throwIt( ISO7816.SW_CONDITIONS_NOT_SATISFIED );

    byte byFreeRecord = (byte)0x7F ;
    byte [] byaRecordData ;

    //@ close [1/2]MyApplet_(this, _, _);
    for (byte i = 0; i < by_NbRecords; i++)
      /*@
      invariant
        [1/2]MyApplet_(this, ?nbRecords, maxSizeRecord) &*&
        array_slice(byaApdu, 0, byaApdu.length, _) &*& 133 <= byaApdu.length &*&
        0 <= i &*& i <= nbRecords &*&
        (byFreeRecord != 0x7F ? 0 <= byFreeRecord &*& byFreeRecord < i : true);
      @*/
    {
      byaRecordData = (byte[]) (o_Records[i]);
      //@ assume(0 <= byaApdu[ADF_LEN_OFFSET] && byaApdu[ADF_LEN_OFFSET] <= 133 - ADF_OFFSET && byaApdu[ADF_LEN_OFFSET] <= byaRecordData.length - ADF_OFFSET);
      if ((byaRecordData[0] != 0x00)
          && Util.arrayCompare(byaApdu, ADF_OFFSET, byaRecordData, (short)(OFF_DATA_IN_RECORD+6), byaApdu[ADF_LEN_OFFSET]) == 0)
        ISOException.throwIt( ISO7816.SW_CONDITIONS_NOT_SATISFIED );
      if (byaRecordData[0] == 0x00)
      {
        byFreeRecord = i ;
      }
      //@ close [1/2]record(by_MaxSizeRecord, byaRecordData, unit);
      //@ close [1/2]MyApplet_(this, _, _);
    }
    //@ assume(11 <= shLC);

    if (byFreeRecord != 0x7F)
    {
      //@ close [1/2]MyApplet_(this, _, _);
      JCSystem.beginTransaction();
      //@ open valid();

      byaRecordData = (byte[])o_Records[byFreeRecord];
      //@ open record(by_MaxSizeRecord, byaRecordData, _);
      Util.arrayCopy(byaApdu, ISO7816.OFFSET_CDATA, byaRecordData, OFF_DATA_IN_RECORD, shLC);
      //@ assume(0 <= byaRecordData[6] && byaRecordData[6] <= by_MaxSizeRecord - 6);
      byaRecordData[0] = (byte)shLC ;
      //@ close record(by_MaxSizeRecord, byaRecordData, _);
      //@ close MyApplet_(this, _, _);
      //@ close valid();
      JCSystem.commitTransaction();
    }
    else
    {

      //@ close [1/2]MyApplet_(this, _, _);
      JCSystem.beginTransaction();
      //@ open valid();
      //@ open MyApplet_(this, _, _);
      if (by_NbRecords >= by_MaxNbRecord)
        ISOException.throwIt( ISO7816.SW_FILE_FULL );
      o_Records[by_NbRecords] = new byte[by_MaxSizeRecord + LEN_RECORD_LEN_BYTE];
      byaRecordData = (byte[])(o_Records[by_NbRecords]);
      by_NbRecords++ ;

      Util.arrayCopy(byaApdu, ISO7816.OFFSET_CDATA, byaRecordData, OFF_DATA_IN_RECORD, shLC);
      //@ assume(0 <= byaRecordData[6] && byaRecordData[6] <= by_MaxSizeRecord - 6);
      byaRecordData[0] = (byte)shLC ;
      //@ close record(by_MaxSizeRecord, byaRecordData, unit);
      //@ close my_record(by_MaxSizeRecord, byaRecordData, unit);
      //@ array_slice_deep_close(o_Records, by_NbRecords - 1, my_record, maxSizeRecord);
      //@ close MyApplet_(this, _, _);
      //@ close valid();
      JCSystem.commitTransaction();
    }
    //@ open valid();
    //@ open MyApplet_(this, _, _);
    if ((byFreeRecord == (byte)0x7F) && (by_NbRecords == 1))
      GPSystem.setCardContentState( GPSystem.SECURITY_DOMAIN_PERSONALIZED );
      //@ close [1/2]MyApplet_(this, _, _);
      //@ close [1/2]valid();
  }

  private static final byte MODE_DELETE_UNSET      = 0 ;
  private static final byte MODE_DELETE_BY_NUMBER  = 1 ;
  private static final byte MODE_DELETE_BY_AID     = 2 ;
  private static final byte MODE_DELETE_BY_REFRESH = 3 ;

  private void processDeleteRecord(APDU oApdu)
    //@ requires current_applet(this) &*& [1/2]valid() &*& oApdu != null &*& APDU(oApdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures current_applet(this) &*& [1/2]valid() &*& oApdu != null &*& APDU(oApdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
  {
    byte[] byaApdu = checkIncomingData(oApdu, true, false);

    byte byMode = MODE_DELETE_UNSET ;
    switch(byaApdu[ISO7816.OFFSET_P2]&0x07)
    {
    case 0x00:
      switch(byaApdu[ISO7816.OFFSET_P1])
      {
      case 0x00 :
        byMode = MODE_DELETE_BY_AID ;
        break ;
      case 0x01 :
        byMode = MODE_DELETE_BY_REFRESH ;
        break ;
      default:
        ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
      }
      break ;
    case 0x04:
      byMode = MODE_DELETE_BY_NUMBER ;
      break ;
    default:
      ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
    }

    if((byaApdu[ISO7816.OFFSET_P2]>>3) != 1)
      ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
    byte [] byaRecordData = null ;
    if (byMode == MODE_DELETE_BY_NUMBER)
    {

      byte byRecordToDelete = /*@ truncating @*/ (byte)(byaApdu[ISO7816.OFFSET_P1]-1) ;
      JCSystem.beginTransaction();
      //@ open valid();
      //@ open MyApplet_(this, _, _);
      if ((byRecordToDelete < by_NbRecords) && (byRecordToDelete >= 0))
        byaRecordData = (byte[])(o_Records[byRecordToDelete]) ;
      //
      if (byaRecordData == null
          || byaRecordData[0] == (byte)0)
        ISOException.throwIt(ISO7816.SW_RECORD_NOT_FOUND);
      //
      byaRecordData[0] = (byte)0 ;
      //@ close record(by_MaxSizeRecord, byaRecordData, unit);
      //@ close MyApplet_(this, _, _);
      //@ close valid();
      JCSystem.commitTransaction();

    }
    else if (byMode == MODE_DELETE_BY_AID)
    {

            JCSystem.beginTransaction(); // Inserted for VeriFast
            //@ open valid();
            //@ open MyApplet_(this, _, _);
            //@ close MyApplet_(this, _, _);
      for(byte i=0 ; i<by_NbRecords ; i++)
        /*@
        invariant
          MyApplet_(this, ?nbRecords, _) &*&
          array_slice(byaApdu, 0, byaApdu.length, _) &*& 133 <= byaApdu.length &*&
          0 <= i &*& i <= nbRecords;
        @*/
      {
        byaRecordData = (byte[])(o_Records[i]) ;

        if (Util.arrayCompare(byaApdu, ISO7816.OFFSET_CDATA,
            byaRecordData, (short)(OFF_DATA_IN_RECORD+6), byaRecordData[OFF_DATA_IN_RECORD+5]) == 0)
        {
          byaRecordData[0] = (byte)0 ;
          //@ close record(by_MaxSizeRecord, byaRecordData, unit);
          //@ close MyApplet_(this, _, _);
          break;
        }
        //@ close record(by_MaxSizeRecord, byaRecordData, unit);
      }
      //@ close valid();
      JCSystem.commitTransaction(); // Inserted for VeriFast. TODO: Move closer to update.
    }
    else if (byMode == MODE_DELETE_BY_REFRESH)
    {
      JCSystem.beginTransaction(); // Inserted for VeriFast
      //@ open valid();
      //@ open MyApplet_(this, _, _);
      //@ close MyApplet_(this, _, _);
      for(short i=0 ; i<by_NbRecords ; i++)
        /*@
        invariant
          MyApplet_(this, ?nbRecords, _) &*&
          array_slice(byaApdu, 0, byaApdu.length, _) &*& 133 <= byaApdu.length &*&
          0 <= i &*& i <= nbRecords;
        @*/
      {
        byaRecordData = (byte[])(o_Records[i]) ;
          if (JCSystem.lookupAID( byaRecordData, (byte)(OFF_DATA_IN_RECORD+6), byaRecordData[OFF_DATA_IN_RECORD+5] )== null)
        {
          byaRecordData[0] = (byte)0;
        }
        //@ close record(by_MaxSizeRecord, byaRecordData, unit);
      }
      //@ close valid();
      JCSystem.commitTransaction();
    }
  }

  private void processReadRecord(APDU oApdu)
    //@ requires [1/2]valid() &*& oApdu != null &*& APDU(oApdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures [1/2]valid() &*& oApdu != null &*& APDU(oApdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
  {
      //@ open valid();
    byte[] byaApdu = checkIncomingData(oApdu, false, true);
    short shIndexRecord = (short)(sh(byaApdu[ISO7816.OFFSET_P1]) - (short)1);

    if ((shIndexRecord < (short)0) || (shIndexRecord >= by_NbRecords))
      ISOException.throwIt(ISO7816.SW_RECORD_NOT_FOUND);
    if((byaApdu[ISO7816.OFFSET_P2]&0x07) != 4)
      ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);

    if((byaApdu[ISO7816.OFFSET_P2]>>3) != 1)
      ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);

    byte [] byaRecordData = (byte[])(o_Records[shIndexRecord]) ;
    short shLenRecord = sh(byaRecordData[0]);

    if (shLenRecord == (short)0)
      ISOException.throwIt(ISO7816.SW_RECORD_NOT_FOUND);

    //@ open is_short_of_byte(shLenRecord, _);
    Util.arrayCopyNonAtomic(byaRecordData, OFF_DATA_IN_RECORD, byaApdu, ISO7816.OFFSET_CDATA, shLenRecord);

    short shLE = oApdu.setOutgoing() ;

    if (shLE == (short)0 || shLE > shLenRecord) shLE = shLenRecord ;

    oApdu.setOutgoingLength(shLE);
    oApdu.sendBytes((short)0, (short)shLE);
    //@ close [1/2]record(by_MaxSizeRecord, byaRecordData, unit);
    //@ close [1/2]MyApplet_(this, _, _);
    //@ close [1/2]valid();
  }

  private short sh(byte byByte)
    //@ requires true;
    //@ ensures is_short_of_byte(result, byByte) &*& 0 <= result &*& result <= 255;
  {
    short res = (short) (byByte & 0xFF);
    return res;
    //@ assume (byByte < 0 ? res == 256 + byByte : res == byByte);
    //@ close is_short_of_byte((short) (byByte & 0xFF), byByte);
  }
  private void askForSharingPoints()
    //@ requires current_applet(this) &*& [1/2]valid();
    //@ ensures current_applet(this) &*& [1/2]valid();
  {
	AID NewEid_AID = JCSystem.lookupAID(NewEidAID,(short)0, (byte)NewEidAID.length);
		
	if (NewEid_AID == null)
		ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
		
	JCSystem.beginTransaction(); // Added for VeriFast
	NewEidPointsObject = (INewEidPoints)
		(JCSystem.getAppletShareableInterfaceObject(NewEid_AID, (byte) 0x00));
		
	INewEidPoints newEidPoints = NewEidPointsObject;
	byte points = Points;
	
	if (newEidPoints != null) {
	    points = newEidPoints.sharePoints(points);
	}
	
	Points = points;
	JCSystem.commitTransaction(); // Added for VeriFast
		
  }

  private void askForPayment()
    //@ requires current_applet(this) &*& [1/2]valid();
    //@ ensures current_applet(this) &*& [1/2]valid();
  {
	AID NewEPurse_AID = JCSystem.lookupAID(NewEPurseAID,(short)0, (byte)NewEPurseAID.length);
		
	if (NewEPurse_AID == null)
		ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
		
	JCSystem.beginTransaction(); // Added for VeriFast
	NewEPurseDebitObject = (IEPurseServicesDebit)
		(JCSystem.getAppletShareableInterfaceObject(NewEPurse_AID, (byte) 0x00));
	IEPurseServicesDebit newEPurseDebitObject = NewEPurseDebitObject;
	byte points = Points;
		
	if (newEPurseDebitObject != null) {
        //@ Shareable epurseServiceSIO = newEPurseDebitObject;
        //@ assert epurseServiceSIO.Shareable(?epurseApplet1);
        //@ mem_registered_applets_is(this);
        //@ assert registered_applets(?as1);
        //@ foreachp_unremove<Applet>(this, as1);
        //@ set_current_applet(epurseApplet1);
        //@ foreachp_remove(epurseApplet1, as1);
	newEPurseDebitObject.debit(points);
        //@ is_registered_applets_mem(this);
        //@ assert registered_applets(?as2);
        //@ foreachp_unremove(epurseApplet1, as2);
        //@ set_current_applet(this);
        //@ foreachp_remove<Applet>(this, as2);
        }
	
	NewEPurseCreditObject = (IEPurseServicesCredit)
	(JCSystem.getAppletShareableInterfaceObject(NewEPurse_AID, (byte) 0x01));
	IEPurseServicesCredit newEPurseCreditObject = NewEPurseCreditObject;
	
	if (newEPurseCreditObject != null) {
        //@ Shareable epurseServiceSIO = newEPurseCreditObject;
        //@ assert epurseServiceSIO.Shareable(?epurseApplet2);
        //@ mem_registered_applets_is(this);
        //@ assert registered_applets(?as1);
        //@ foreachp_unremove<Applet>(this, as1);
        //@ set_current_applet(epurseApplet2);
        //@ foreachp_remove(epurseApplet2, as1);
	newEPurseCreditObject.transaction(points);
        //@ is_registered_applets_mem(this);
        //@ assert registered_applets(?as2);
        //@ foreachp_unremove(epurseApplet2, as2);
        //@ set_current_applet(this);
        //@ foreachp_remove<Applet>(this, as2);
        }
	
	JCSystem.commitTransaction(); // Added for VeriFast
  }
  
  public Shareable getShareableInterfaceObject(AID oAid, byte bArg)
        //@ requires [1/2]this.valid() &*& registered_applets(?as) &*& foreachp(remove<Applet>(this, as), semi_valid) &*& mem<Applet>(this, as) == true &*& AID(oAid);
        //@ ensures [1/2]this.valid() &*& registered_applets(as) &*& foreachp(remove<Applet>(this, as), semi_valid) &*& AID(oAid) &*& result == null ? true : result.Shareable(?a) &*& mem<Applet>(a, as) == true;
  {
		
		//check if AID is allowed
		//@ NewMyAppletPointsObject.getShareable();
		
		if (bArg == (byte)0x0) // Based on argument, return
												// object reference
			return (Shareable) (NewMyAppletPointsObject);

          else 
			    ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		
		return null; //~allow_dead_code
	}
}

//@ predicate is_short_of_byte(short s, byte b) = b < 0 ? s == 256 + b : s == b;
