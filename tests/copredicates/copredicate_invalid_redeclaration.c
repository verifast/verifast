//@ predicate mycopredicate(int x);
//@ copredicate mycopredicate(int x) = mycopredicate(x*2);  //~ should fail
