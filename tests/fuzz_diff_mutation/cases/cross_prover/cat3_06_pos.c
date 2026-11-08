void array_write(int *arr)
//@ requires arr[0..3] |-> ?vs;
//@ ensures arr[0..3] |-> update(0, 42, vs);
{
    arr[0] = 42;
}
