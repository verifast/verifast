package newepurse;

import javacard.framework.*;

public interface IEPurseServicesDebit extends Shareable {

    public void debit(short amount) throws ISOException /*@ ensures true; @*/;
        //@ requires Shareable(?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures Shareable(a) &*& in_transaction(a) &*& a.valid();

}
