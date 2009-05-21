/*@

inductive okay1 = okay1(okay2);

inductive okay2 = okay2(int, void *, unit);

inductive foo = foo(bar);

inductive bar = bar1(foo) | bar2(bar) | bar3(foo, bar); //~ should fail

@*/