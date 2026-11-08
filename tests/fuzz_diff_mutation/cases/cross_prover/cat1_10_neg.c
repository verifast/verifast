void f(int x, int y)
//@ requires x >= 1 &*& y >= 1;
//@ ensures x + y >= 3; //~should_fail
{}
