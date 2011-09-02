import javacard.framework.*;

public final class MyApplet extends Applet {
    int tokensLeft, tokensUsed;
    
    //@ predicate valid() = tokensLeft |-> ?m &*& 0 <= m &*& tokensUsed |-> ?n &*& m + n == 10;
    
    MyApplet()
        //@ requires true;
        //@ ensures valid();
    {
        tokensLeft = 10;
    }
    
    public static void install(byte[] array, short offset, byte length) 
        //@ requires system();
        //@ ensures true;
    {
        MyApplet applet = new MyApplet();
        applet.register();
    }
    
    public void process(APDU apdu)
        //@ requires current_applet(this) &*& [1/2]valid();
        //@ ensures current_applet(this) &*& [1/2]valid();
    {
        //@ { int x = tokensLeft + tokensUsed; assert x == 10; }
        if (tokensLeft == 0)
            ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
        JCSystem.beginTransaction();
        //@ open valid();
        tokensLeft--;
        tokensUsed++;
        JCSystem.commitTransaction();
    }
}