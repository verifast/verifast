/*@
predicate a_predicate();

lemma void test()
requires [_][_]a_predicate(); //~ should-fail
ensures true;
{
}
@*/
