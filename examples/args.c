void puts(char *s);
    //@ requires [?f]chars(s, ?cs) &*& mem('\0', cs) == true;
    //@ ensures [f]chars(s, cs);

/*@

lemma void pointer_is_in_range(void **p);
    requires [?f]pointer(p, ?v);
    ensures [f]pointer(p, v) &*& true == ((void **)0 <= p) &*& p <= (void **)4294967295;
@*/

int main0(int argc, char **argv)
    //@ requires 0 <= argc &*& [_]argv(argv, argc);
    //@ ensures true;
{
    for (int i = 0; i<argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv + i, argc - i);
    {
        //@ open argv(argv + i, argc - i);
        //@ pointer_is_in_range(argv + i);
        puts(*(argv + i));
    }
    //@ open argv(_, 0);
    return 0;
}