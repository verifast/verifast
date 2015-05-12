public final class InstancePredicateUseInLemma{
    //@ predicate pred(list<char> nm) = nm == nil;
    private String name;

}
/*@
  lemma void mylemma(InstancePredicateUseInLemma obj)
  requires obj.pred(?nm);
  ensures obj.pred(nm);
  {
   open obj.pred(nm);
   close obj.pred(nm);
  }
@*/
