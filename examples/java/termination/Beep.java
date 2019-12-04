//@ predicate IO(int n);

class OS {

    static void beep()
        //@ requires IO(?n);
        //@ ensures 0 < n &*& IO(n - 1);
        //@ terminates;
    {
        throw new RuntimeException();
    }

}

class Beeper {

    static void beepForever()
        //@ requires IO(?n) &*& call_perm_rec(currentThread, {Beeper.class}, int_lt, n);
        //@ ensures false;
        //@ terminates;
    {
        OS.beep();
        //@ call_perm_rec_weaken(2, n - 1);
        //@ call_perm_rec_elim(1);
        //@ consume_call_perm_for(Beeper.class);
        beepForever();
    }

}

class Main {

    static void main()
        //@ requires IO(?n);
        //@ ensures false;
        //@ terminates;
    {
        //@ produce_call_below_perm_();
        //@ is_wf_int_lt();
        //@ call_below_perm__elim_rec(1, {Beeper.class}, int_lt, n);
        Beeper.beepForever();
    }

}
