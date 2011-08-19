package wallet;

import javacard.framework.*;

///@ predicate_family EInterface(Class c)(EWalletInterface eInterface);

public interface EWalletInterface extends Shareable {
    public void verify(byte[] pincode, short offset, byte length);
     //@ requires array_slice(pincode, 0, pincode.length,_) &*& registered_applets(?as) &*& shareable_interface_object(this.getClass())(this, ?a) &*& foreach<Applet>(remove<Applet>(a, as),full_valid) &*& a.valid() &*& mem<Applet>(a,as)==true; //&*& EInterface(this.getClass())(this);
    //@ ensures array_slice(pincode, 0, pincode.length,_) &*& registered_applets(as) &*& shareable_interface_object(this.getClass())(this, a) &*& foreach<Applet>(remove<Applet>(a, as),full_valid) &*& a.valid() &*& mem<Applet>(a,as)==true; //EInterface(this.getClass())(this);
    public void debit(byte amount);
     //@ requires 0 <= amount &*& registered_applets(?as) &*& shareable_interface_object(this.getClass())(this, ?a) &*& foreach<Applet>(remove<Applet>(a, as),full_valid) &*& a.valid() &*& mem<Applet>(a,as)==true; //EInterface(this.getClass())(this);
    //@ ensures registered_applets(as) &*& shareable_interface_object(this.getClass())(this, a) &*& foreach<Applet>(remove<Applet>(a, as),full_valid) &*& a.valid() &*& mem<Applet>(a,as)==true; //EInterface(this.getClass())(this);
}
