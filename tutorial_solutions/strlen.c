int strlen(char *s)
    //@ requires [?f]string(s, ?cs);
    //@ ensures [f]string(s, cs) &*& result == length(cs);
{
    char *c = s;
    for (;;)
        //@ requires [f]string(c, ?cs1);
        //@ ensures [f]string(old_c, cs1) &*& c - old_c == length(cs1);
    {
        //@ open [f]string(c, cs1);
        if (*c == 0) {
            //@ close [f]string(c, cs1);
            break;
        }
        c++;
        //@ recursive_call();
        //@ close [f]string(old_c, cs1);
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
