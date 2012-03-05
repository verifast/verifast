package newepurse;

import javacard.framework.*;

public interface IEPurseServicesCredit extends Shareable {

    public void charge(short amount);
        //@ requires Shareable(?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures Shareable(a) &*& in_transaction(a) &*& a.valid();
    public void transaction(short amount);
        //@ requires Shareable(?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures Shareable(a) &*& in_transaction(a) &*& a.valid();

}
