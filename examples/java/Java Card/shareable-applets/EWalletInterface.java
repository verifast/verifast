package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {

    public void verify(byte[] pincode, short offset, byte length);
        //@ requires array_slice(pincode, 0, pincode.length, _) &*& Shareable(?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures array_slice(pincode, 0, pincode.length, _) &*& Shareable(a) &*& in_transaction(a) &*& a.valid();
    
    public void debit(byte amount);
        //@ requires 0 <= amount &*& Shareable(?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures Shareable(a) &*& in_transaction(a) &*& a.valid();
    
}
