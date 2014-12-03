//@ predicate integer(int *p; int v) = false &*& v == 0;

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
