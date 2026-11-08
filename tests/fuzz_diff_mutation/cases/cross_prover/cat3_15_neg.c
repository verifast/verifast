void write_unheld_neg(int *p)
//@ requires true;
//@ ensures true;
{
    *p = 5; //~should_fail
}
