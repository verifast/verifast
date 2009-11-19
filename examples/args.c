void puts(char *s);
    //@ requires [?f]chars(s, ?cs) &*& mem('\0', cs) == true;
    //@ ensures [f]chars(s, cs);

/*@

predicate argv(char **argv, int argc)
    requires argc <= 0 ? emp : [_]pointer(argv, ?arg) &*& [_]chars(arg, ?argChars) &*& mem('\0', argChars) == true &*& argv(argv + 1, argc - 1);

lemma void pointer_is_in_range(void **p);
    requires [?f]pointer(p, ?v);
    ensures [f]pointer(p, v) &*& true == ((void **)0 <= p) &*& p <= (void **)4294967295;
@*/

int main0(int argc, char **argv)
    //@ requires 0 <= argc &*& argv(argv, argc);
    //@ ensures true;
{
    int i = 0;
    while (i < argc)
        //@ invariant 0 <= i &*& i <= argc &*& argv(argv + i, argc - i);
    {
        //@ open argv(argv + i, argc - i);
        //@ pointer_is_in_range(argv + i);
        puts(*(argv + i));
        i = i + 1;
    }
    //@ open argv(_, 0);
    return 0;
}