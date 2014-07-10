/*@
copredicate mycopredicate() = mycopredicate();

predicate mypredicate(int x) =
  x < 0 ? emp : mypredicate(x - 1);

predicate whatever() = false;

lemma void valid_recursion()
requires mypredicate(?x) &*& mycopredicate();
ensures mycopredicate();
{
  open mycopredicate();
  open mypredicate(x);
  if (x >= 0){
    valid_recursion();
  }
}

@*/
