#define LLONG_MAX 9223372036854775807

long long incr(long long x)
    //@ requires x < LLONG_MAX;
    //@ ensures result == x + 1;
{
    return x + 1;
}
