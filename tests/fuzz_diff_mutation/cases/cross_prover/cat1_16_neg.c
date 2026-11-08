void f(int x, int y)
//@ requires x < y;
//@ ensures x + 1 < y; //~should_fail
{}
