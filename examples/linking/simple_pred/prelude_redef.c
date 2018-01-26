//@ predicate malloc_block(void *p; int size) = false &*& size == 0;

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
