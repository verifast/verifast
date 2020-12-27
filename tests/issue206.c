// https://github.com/verifast/verifast/issues/206

int foo_good()
    /*@ requires true; @*/
    /*@ ensures  result == 3*7*6; @*/
    /*@ terminates; @*/
{
    int x = 0;
    int i,j,k;

    for(i = 0; i < 6; ++i)
        /*@ requires i >= 0 &*& i <= 6 &*& x + 3*7*(6-i) < 100000; @*/
        /*@ ensures x == old_x + 3*7*(i - old_i); @*/
        /*@ decreases 6-i; @*/
    {
        for(j = 0; j < 7; ++j)
            /*@ requires j >= 0 &*& j <= 7 &*& x + 3*(7-j) < 100000; @*/
            /*@ ensures x == old_x + 3*(j - old_j); @*/
            /*@ decreases 7-j; @*/
        {
            for(k = 0; k < 3; ++k)
                /*@ requires k >= 0 &*& k <= 3 &*& x + (3-k) < 100000; @*/
                /*@ ensures  old_x + (3-old_k) == x; @*/
                /*@ decreases 3-k; @*/
            {
                ++x;
            }
        }
    }
    return x;
}

int foo_bad()
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
    /*@ terminates; @*/
{
    int x = 0;
    int i,j,k;

    for(i = 0; i < 6; )
        /*@ requires i >= 0 &*& i <= 6 &*& x + 3*7*(6-i) < 100000; @*/
        /*@ ensures  old_x == x; @*/
        /*@ decreases 6-i; @*/
    {
        for(j = 0; j < 7; ++j)
            /*@ requires j >= 0 &*& j <= 7 &*& x + 3*(7-j) < 100000; @*/
            /*@ ensures  old_x == x; @*/ //~ should_fail
            /*@ decreases 7-j; @*/
        {
            for(k = 0; k < 3; ++k)
                /*@ requires k >= 0 &*& k <= 3 &*& x + (3-k) < 100000; @*/
                /*@ ensures  old_x + (3-old_k) == x; @*/
                /*@ decreases 3-k; @*/
            {
                ++x;
            }
        }
    }
}
