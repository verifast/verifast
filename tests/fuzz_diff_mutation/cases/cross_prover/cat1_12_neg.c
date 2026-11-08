void f(int x, int y)
//@ requires x == 17 &*& y == 5;
//@ ensures x % y == 1; //~should_fail
{}
