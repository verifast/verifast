/*@

predicate bar() = true;

typedef lemma void foo();
    requires true;
    ensures bar();

lemma void test(foo *f)
    requires is_foo(f);
    ensures is_foo(f) &*& bar();
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
    produce_lemma_function_pointer_chunk(quux) {
      test(quux);
    }
}

@*/