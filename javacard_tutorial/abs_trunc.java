class Program {
    static short abs(short x)
        //@ requires true;
        //@ ensures true; //0 <= result &*& result == x || result == -x;
    {
        if (x < 0) {
            x = /*@truncating@*/(short)-x;
            return x;
        } else {
            return x;
        }
    }
}
