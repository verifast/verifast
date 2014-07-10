/*@
copredicate mycopredicate() = mycopredicate();

predicate something();

lemma void some_induction(predicate() p);
requires p();
ensures something();

lemma void use_some_induction()
requires mycopredicate();
ensures something();
{
  some_induction(mycopredicate); //~ should fail
}

@*/
