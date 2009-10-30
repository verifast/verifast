/*@
inductive ints = ints_nil | ints_cons(int, ints);

fixpoint int ints_length(ints is) {
  switch(is) {
    case ints_nil: return 0;
    case ints_cons(h, t): return 1 + ints_length(t);
  }
}

lemma_auto void ints_length_positive(ints is) 
  requires true;
  ensures 0 <= ints_length(is);
{
  switch(is) {
    case ints_nil: ;
    case ints_cons(h, t): ints_length_positive(t);
  }
}

fixpoint int ints_length2(ints is) {
  switch(is) {
    case ints_nil: return 0;
    case ints_cons(h, t): return 1 + ints_length2(t);
  }
}

lemma_auto void ints_length2_positive(ints is);
  requires true;
  ensures 0 <= ints_length2(is);

predicate p(ints is) = true;
@*/

void m()
  //@ requires p(?is);
  //@ ensures p(is) &*& 0 <= ints_length(is);
{
}

void m2()
  //@ requires p(?is);
  //@ ensures p(is) &*& 0 <= ints_length2(is);
{
}

