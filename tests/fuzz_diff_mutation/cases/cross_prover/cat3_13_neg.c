int array_oob_neg(int *arr)
//@ requires arr[0..3] |-> ?vs;
//@ ensures arr[0..3] |-> vs;
{
    return arr[3]; //~should_fail
}
