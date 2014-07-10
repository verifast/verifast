/*@
copredicate mycopredicate() = mycopredicate();

predicate something() = false;

lemma void wrong_coinduction()
requires mycopredicate();
ensures something();
{
  wrong_coinduction(); //~ should fail
}

@*/
