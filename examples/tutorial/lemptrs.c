//@ predicate small_string(char *s) = string(s, ?characters) &*& length(characters) <= 20;
//@ predicate large_string(char *s) = string(s, ?characters) &*& length(characters) <= 1000;

char **read_lines();
//@ requires true;
//@ ensures result[..100] |-> ?lines &*& foreach(lines, small_string);

void write_lines(char **p);
//@ requires p[..100] |-> ?lines &*& foreach(lines, large_string);
//@ ensures true;

/*@

typedef lemma void conversion_lemma<t>(predicate(t) P, predicate(t) Q)();
    requires P(?x);
    ensures Q(x);

lemma void convert_foreach<t>()
    requires foreach<t>(?xs, ?P) &*& is_conversion_lemma(?convert, P, ?Q);
    ensures foreach<t>(xs, Q) &*& is_conversion_lemma(convert, P, Q);
{
    open foreach(xs, P);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            convert();
            convert_foreach();
    }
    close foreach(xs, Q);
}

lemma void foreach_small_large_string()
    requires foreach(?strings, small_string);
    ensures foreach(strings, large_string);
{
    produce_lemma_function_pointer_chunk conversion_lemma<char *>(small_string, large_string)() {
        open small_string(?s);
        close large_string(s);
    } {
        convert_foreach();
    }
}

@*/

int main()
//@ requires true;
//@ ensures true;
{
    char **p = read_lines();
    //@ foreach_small_large_string();
    write_lines(p);
    return 0;
}
