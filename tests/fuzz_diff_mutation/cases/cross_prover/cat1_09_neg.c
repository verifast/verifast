void f(int x, int y)
//@ requires x <= y;
//@ ensures x < y; //~should_fail
{}
