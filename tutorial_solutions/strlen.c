int strlen(char *s)
    //@ requires [?f]string(s, ?cs);
    //@ ensures [f]string(s, cs) &*& result == length(cs);
{
    int i = 0;
    for (;; i++)
        //@ requires [f]string(s + i, ?cs1);
        //@ ensures [f]string(s + old_i, cs1) &*& i == old_i + length(cs1);
    {
        //@ open [f]string(s + i, cs1);
        if (s[i] == 0) {
            break;
        }
    }
    return i;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    int n = strlen("Hello, world!");
    assert(n == 13);
    return 0;
}
