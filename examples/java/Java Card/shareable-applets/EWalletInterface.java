package wallet;

import javacard.framework.Shareable;

/*@
predicate_family EInterface(Class c)(EWalletInterface eInterface);
@*/

public interface EWalletInterface extends Shareable {
    public void verify(byte[] pincode, short offset, byte length);
     //@ requires array_slice(pincode,offset,length,_) &*& EInterface(this.getClass())(this);
    //@ ensures array_slice(pincode,offset,length,_) &*& EInterface(this.getClass())(this);
    public void debit(byte amount);
     //@ requires 0 <= amount &*& EInterface(this.getClass())(this);
    //@ ensures EInterface(this.getClass())(this);
}
