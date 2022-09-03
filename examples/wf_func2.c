/*@

fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

@*/

void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _;
//@ ensures buf[..length] |-> n_times(c, length);
{
    for (int i = 0; i < length; i++)
    //@ requires i <= length &*& chars_(buf + i, length - i, ?cs0) &*& switch (cs0) { case nil: return true; case cons(c0, cs00): return true; };
    //@ ensures buf[old_i..length] |-> n_times(c, length - old_i);
    {
        buf[i] = c;
    }
}
