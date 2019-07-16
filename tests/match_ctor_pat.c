/*@

inductive foo = bar(int);

lemma void test(foo f)
    requires switch (f) {
                case bar(y): return bar(23);
            } != bar(23);
    ensures false;
{
    assert f == bar(?z);
}

@*/
