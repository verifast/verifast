int div(int x, int y)
//@ requires (y != 0) && !((x == INT_MIN) && (y == -1));
//@ ensures true;
{
    return x / y;
}