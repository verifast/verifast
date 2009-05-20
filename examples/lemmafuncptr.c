/*@

predicate bar() = true;

typedef lemma void foo();
    requires true;
    ensures bar();

lemma void test(foo *f)
    requires is_foo(f) == true;
    ensures bar();
{
    f();
}

lemma void quux() : foo
    requires true;
    ensures bar();
{
    close bar();
}

lemma void test2()
    requires true;
    ensures bar();
{
    test(quux);
}

@*/