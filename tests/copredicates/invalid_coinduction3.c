/*@
predicate mypredicate() = mypredicate2();
predicate mypredicate2() = mycopredicate();

copredicate mycopredicate() = mypredicate();

predicate something() = false;

lemma void wrong_coinduction()
requires mypredicate();
ensures something();
{
  open mypredicate();
  open mypredicate2();
  open mycopredicate(); //~ should fail
  //wrong_coinduction(); 
}

@*/
