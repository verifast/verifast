int strlen(char *s)
    //@ requires [?f]chars(s, ?n, ?cs) &*& mem('\0', cs) == true;
    //@ ensures [f]chars(s, n, cs) &*& result == index_of('\0', cs);
{
    char *c = s;
    for (;;)
        //@ requires [f]chars(c, ?n1, ?cs1) &*& mem('\0', cs1) == true;
        //@ ensures [f]chars(old_c, n1, cs1) &*& c - old_c == index_of('\0', cs1);
    {
        //@ open [f]chars(c, n1, cs1);
        if (*c == 0) {
            //@ close [f]chars(c, n1, cs1);
            break;
        }
        c++;
        //@ recursive_call();
        //@ close [f]chars(old_c, n1, cs1);
    }
    return c - s;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    int n = strlen("Hello, world!");
    assert(n == 13);
    return 0;
}
