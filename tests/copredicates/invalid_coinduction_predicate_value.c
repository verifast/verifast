/*@
copredicate mycopredicate() = mycopredicate();

predicate something();

lemma void some_induction(predicate() p)
requires p() &*& p == mycopredicate;
ensures something();
{
  open p(); //~ should-fail
  //some_induction(p);
}
@*/
