//@ predicate pred(list<char> nm) = nm == nil;

/*@
  lemma void mylemma()
  requires pred(?nm);
  ensures pred(nm);
  {
   open pred(nm);
   close pred(nm);
  }
@*/
