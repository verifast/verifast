package wallet;

import javacard.framework.*;

public interface EWalletInterface extends Shareable {
    
    public void verify(byte[] pincode, short offset, byte length);
        //@ requires array_slice(pincode, 0, pincode.length, _) &*& shareable_interface_object(this.getClass())(this, ?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures array_slice(pincode, 0, pincode.length, _) &*& shareable_interface_object(this.getClass())(this, a) &*& in_transaction(a) &*& a.valid();
    
    public void debit(byte amount);
        //@ requires 0 <= amount &*& shareable_interface_object(this.getClass())(this, ?a) &*& in_transaction(a) &*& a.valid();
        //@ ensures shareable_interface_object(this.getClass())(this, a) &*& in_transaction(a) &*& a.valid();
    
}
