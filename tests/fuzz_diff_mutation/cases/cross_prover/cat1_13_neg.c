void f(int x, int y, int z)
//@ requires x < y &*& z < y;
//@ ensures x < z; //~should_fail
{}
