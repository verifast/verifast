void f(int x, int y)
//@ requires x <= y;
//@ ensures 2*x <= y; //~should_fail
{}
