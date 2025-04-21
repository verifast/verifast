public class LeftPad {

    static char[] leftPad(char c, int n, char[] s)
    //@ requires [?f]s[..] |-> ?cs &*& 0 <= n;
    /*@
    ensures
        [f]s[..] |-> cs &*&
        result.length == max(s.length, n) &*&
        result[..result.length - s.length] |-> repeat(nat_of_int(result.length - s.length), c) &*&
        result[result.length - s.length..] |-> cs;
    @*/
    {
        int pad = Math.max(n - s.length, 0);
        char[] v = new char[pad + s.length];
        int i = 0;

        for(; ; i++)
        //@ requires 0 <= i &*& i <= pad &*& v[i..pad] |-> _;
        //@ ensures i == pad &*& v[old_i..pad] |-> repeat(nat_of_int(pad - old_i), c);
        {
            if (i == pad) {
                //@ assert v[i..pad] |-> ?cs0;
                //@ switch (cs0) { default: }
                break;
            }
            //@ succ_int(pad - i - 1);
            v[i] = c;
        }
        
        for(; ; i++)
        //@ requires pad <= i &*& [f]s[i - pad..] |-> ?cs1 &*& v[i..] |-> _;
        //@ ensures [f]s[old_i - pad..] |-> cs1 &*& v[old_i..] |-> cs1;
        {
            //@ switch (cs1) { default: }
            if (i == v.length) {
                //@ assert v[i..] |-> ?cs0;
                //@ switch (cs0) { default: }
                break;
            }
            v[i] = s[i - pad];
        }
        
        return v;
    }
    
}