#include <math.h>

double my_sqrt(double x)
    //@ requires true;
    //@ ensures true;
{
    if (x == 0) return 0;
    double result = 1;
    for (;;)
        //@ invariant true;
    {
        double oldResult = result;
        result = (result + (long double)x / result) / 2;
        double step = fabs(result - oldResult);
        if (step < 0.000004*result) {
            break;
        }
    }
    return result;
}

float vector_size(float x, float y)
    //@ requires true;
    //@ ensures true;
{
    double result = my_sqrt((double)x * x + (double)y * y);
    return (float)result;
}
