void foo(char *buffer)
    //@ requires [1/2]chars(buffer, 10, _);
    //@ ensures chars(buffer, 10, _); //~ should_fail
{
}
