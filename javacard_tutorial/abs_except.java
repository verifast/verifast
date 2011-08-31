import javacard.framework.*;

class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures 0 <= result &*& result == x || result == -x;
    {
        if (x == -32768)
            ISOException.throwIt(ISO7816.SW_UNKNOWN);
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}
