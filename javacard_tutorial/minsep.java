class Program {
    static short min(short x, short y, short z)
        //@ requires true;
        /*@
        ensures
            result <= x &*& result <= y &*& result <= z &*&
            (result == x || result == y || result == z);
        @*/
    {
        if (x < y) {
            if (x < z) {
                return x;
            } else {
                return z;
            }
        } else {
            return y;
        }
    }
}
