/*@
copredicate mycopredicate() = mycopredicate();

predicate something() = false;

lemma void wrong_coinduction()
requires mycopredicate();
ensures something();
{
  open mycopredicate(); //~ should fail
  //wrong_coinduction(); 
}

@*/
