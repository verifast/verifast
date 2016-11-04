//@ #include "quantifiers.gh"

/*@
lemma t not_forall<t>(list<t> vs, fixpoint(t, bool) p)
  requires ! forall(vs, p);
  ensures mem(result, vs) == true &*& ! p(result);
{
  switch(vs) {
    case nil: return default_value<t>;
    case cons(h, t):
      if(! p(h)) {
        return h;
      } else {
        return not_forall(t, p);
      }
  }
}

lemma void forall_elim<t>(list<t> vs, fixpoint(t, bool) p, t x)
  requires forall(vs, p) == true &*& mem(x, vs) == true;
  ensures p(x) == true;
{
  switch(vs) {
    case nil:
    case cons(h, t):
      if(h != x) {
        forall_elim(t, p, x);
      }
  }
}
  
lemma int not_forall_nth_nat<t>(list<t> vs, fixpoint (list<t>, int, bool) p, nat n)
  requires ! forall_nth_core(vs, p, n);
  ensures 0 <= result &*& result <= int_of_nat(n) &*& ! p(vs,result);
{
  switch(n) {
    case zero: return 0;
    case succ(n0):
      if( ! p(vs, int_of_nat(n))) {
        return int_of_nat(n);
      } else {
        int i = not_forall_nth_nat(vs, p, n0);
        return i;
      }
  }
}

lemma int not_forall_nth<t>(list<t> vs, fixpoint (list<t>, int, bool) p)
  requires ! forall_nth(vs, p);
  ensures 0 <= result &*& result < length(vs) &*& ! p(vs, result);
{
  switch(vs) {
    case nil: return 0;
    case cons(h, t):
      int i = not_forall_nth_nat(vs, p, nat_of_int(length(vs) - 1));
      assert i <= int_of_nat(nat_of_int(length(vs) - 1));
      int_of_nat_of_int(length(vs) - 1);
      assert i <= length(vs) - 1;
      return i;
  }
}
  
lemma void forall_nth_elim_nat<t>(list<t> vs, fixpoint (list<t>, int, bool) p, nat n, int i)
  requires forall_nth_core(vs, p, n) == true &*& 0 <= i && i <= int_of_nat(n);
  ensures p(vs, i) == true;
{
  switch(n) {
    case zero:
    case succ(n0):
      if(i == int_of_nat(n)) {
      } else {
          forall_nth_elim_nat(vs, p, n0, i);
      } 
  }
}


lemma void forall_nth_elim<t>(list<t> vs, fixpoint (list<t>, int, bool) p, int i)
  requires forall_nth(vs, p) == true &*& 0 <= i &*& i < length(vs);
  ensures p(vs, i) == true;
{
  switch(vs) {
    case nil:
    case cons(h, t): forall_nth_elim_nat(vs, p, nat_of_int(length(vs) - 1), i);
  }
}



lemma void apply_forall_proof<t>(forall_proof_t *forall_proof, fixpoint(t, bool) p, predicate() pred)
  requires is_forall_proof_t<t>(forall_proof, p, pred) &*& pred();
  ensures [_]is_forall_t<t>(?f) &*& true == f(p) &*& is_forall_proof_t<t>(forall_proof, p, pred) &*& pred();
{
  fixpoint(fixpoint(t, bool),bool) f = get_forall_t<t>();
  if (! f(p)){
    t witness = not_forall_t(f, p);
    forall_proof(witness);
  }
}
@*/
