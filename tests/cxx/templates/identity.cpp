template <typename T>
T identity(const T x)
//@ requires true; 
//@ ensures result == x;
{
    return x;
}
