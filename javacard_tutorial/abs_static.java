class Program {
    static short abs(short x)
        //@ requires x != -32768;
        //@ ensures 0 <= result &*& result == x || result == -x;
    {
        if (x < 0) {
            x = (short)-x;
            return x;
        } else {
            return x;
        }
    }
}
