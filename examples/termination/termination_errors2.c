typedef void func();
    //@ requires true;
    //@ ensures true;

void some_func() //@ : func
    //@ requires true;
    //@ ensures true;
    //@ terminates;
{
    func *f = some_func;
    f(); //~ should_fail
}