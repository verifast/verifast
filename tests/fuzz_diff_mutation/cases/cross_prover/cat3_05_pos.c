int array_read(int *arr)
//@ requires arr[0..3] |-> ?vs;
//@ ensures arr[0..3] |-> vs &*& result == nth(0, vs);
{
    return arr[0];
}
