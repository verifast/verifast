/*@

typedef lemma void foo(foo *f);
    requires is_foo(f);
    ensures false;

lemma void bar(foo *f) : foo
    requires is_foo(f);
    ensures false;
{
    f(f); //~ should_fail
}

lemma void quux()
    requires true;
    ensures false;
{
    produce_lemma_function_pointer_chunk(bar);
    bar(bar);
}

@*/