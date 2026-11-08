void f(int x)
//@ requires 0 <= x &*& x < 100;
//@ ensures x + 5 < 100; //~should_fail
{}
