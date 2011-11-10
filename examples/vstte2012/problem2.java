/*@
inductive term = K | S | apply(term, term);

fixpoint boolean is_value(term t) {
  switch(t) {
    case K: return true;
    case S: return true;
    case apply(left, right): 
      return switch(left) {
        case K: return true;
        case S: return true;
        case apply(leftleft, leftright):
          return switch(leftleft) {
            case K: return is_value(right) && is_value(leftright);
            case S: return true;
            case apply(leftleftleft, leftleftright):
              return leftleftleft == S ? is_value(leftleftright) && is_value(leftright) && is_value(right) : false;
          };
      };
  }
}

fixpoint option<term> step(term t) {
  switch(t) {
    case K: return none; // value
    case S: return none; // value
    case apply(left, right):
      return switch(left) {
        case K: return switch(step(right)) {
          case none: return none; // value
          case some(reduced): return some(apply(K, reduced)); // rec
        };
        case S: return switch(step(right)) {
          case none: return none; // value
          case some(reduced): return some(apply(S, reduced)); // rec
        };
        case apply(leftleft, leftright):
          return switch(leftleft) {
            case K: 
              return switch(step(leftright)) {
                case none: return switch(step(right)) { 
                  case none: return some(leftright); // step
                  case some(reduced): return some(apply(apply(K, leftright), reduced)); // rec
                };
                case some(reduced): return some(apply(apply(K, reduced), right)); // rec
              };
            case S: return switch(step(leftright)) {
                case none: return switch(step(right)) { 
                  case none: return none; // value
                  case some(reduced): return some(apply(apply(S, leftright), reduced)); // rec
                };
                case some(reduced): return some(apply(apply(S, reduced), right)); // rec
              };
            case apply(leftleftleft, leftleftright):
              return switch(leftleftleft) {
                case K: return switch(step(left)) {
                      case none: return switch(step(right)) {
                        case none: return none;
                        case some(reduced): return some(apply(left, reduced));
                      };
                      case some(reduced): return some(apply(reduced, right));
                    };
                case S: return switch(step(leftleftright)) {
                  case none: return switch(step(leftright)) {
                    case none: return switch(step(right)) {
                      case none: return some(apply(apply(leftleftright, right), apply(leftright, right))); // step
                      case some(reduced): return some(apply(apply(apply(S, leftleftright), leftright), reduced)); // rec
                    };
                    case some(reduced): return some(apply(apply(apply(S, leftleftright), reduced), right)); // rec
                  };
                  case some(reduced): return some(apply(apply(apply(S, reduced), leftright), right)); // rec
                };
                case apply(leftleftleftleft, leftleftleftright): //((((llll, lllr), llr), lr), r)
                  return switch(step(left)) {
                      case none: return switch(step(right)) {
                        case none: return none;
                        case some(reduced): return some(apply(left, reduced));
                      };
                      case some(reduced): return some(apply(reduced, right));
                    };
                  };
              };
          };
  }
}

lemma void step_ignore_context(term t, term t2)
  requires step(t2) == none;
  ensures switch(step(t)) { case none: return true; case some(treduced): return switch(step(apply(t, t2))) { case none: return false; case some(reduced): return reduced == apply(treduced, t2); }; };
{
  switch(t) {
    case K: 
    case S: 
    case apply(left, right):
      switch(left) {
        case K: switch(step(right)) {
          case none: 
          case some(reduced):
        };
        case S: switch(step(right)) {
          case none: 
          case some(reduced): 
        };
        case apply(leftleft, leftright):
          switch(leftleft) {
            case K: 
              switch(step(leftright)) {
                case none: switch(step(right)) { 
                  case none: 
                  case some(reduced):
                };
                case some(reduced):
              };
            case S: switch(step(leftright)) {
                case none: switch(step(right)) { 
                  case none: 
                  case some(reduced): 
                };
                case some(reduced): 
              };
            case apply(leftleftleft, leftleftright): // (((lll, llr), lr), r)
              switch(leftleftleft) {
                case K: switch(step(leftleftright)) {
                    case none: switch(step(leftright)) {
                      case none: 
                      case some(reduced): some(apply(apply(apply(K, leftleftright), reduced), right)); // rec
                    };
                    case some(reduced): some(apply(apply(apply(K, reduced), leftright), right)); // rec
                  };
                case S: switch(step(leftleftright)) {
                  case none: switch(step(leftright)) {
                    case none: switch(step(right)) {
                      case none:
                      case some(reduced):
                    };
                    case some(reduced):
                  };
                  case some(reduced):
                };
                case apply(leftleftleftleft, leftleftleftright): // ((((_, _), _), _), _)
              };
          };
      };
  }
}



lemma void nsteps_ignore_context_core(nat m, term t, term reduced, term t2)
  requires exists<nat>(m) &*& nsteps(m, t) == reduced &*& step(t2) == none;
  ensures exists<nat>(?m2) &*& nsteps(m2, apply(t, t2)) == apply(reduced, t2);
{
  switch(m) {
    case zero:
    case succ(m0): switch(step(nsteps(m0, t))) {
      case none:
        open exists<nat>(m);
        close exists<nat>(m0);
        nsteps_ignore_context_core(m0, t, reduced, t2);
      case some(reduced0): 
        open exists<nat>(m);
        close exists<nat>(m0);
        nsteps_ignore_context_core(m0, t, nsteps(m0, t), t2);
        step_ignore_context(nsteps(m0, t), t2);
        open exists(?newm);
        close exists(succ(newm));
    }
  }
}

lemma void nsteps_ignore_context(term t, term reduced, term t2)
  requires exists<nat>(?m) &*& nsteps(m, t) == reduced &*& step(t2) == none;
  ensures exists<nat>(?m2) &*& nsteps(m2, apply(t, t2)) == apply(reduced, t2);
{
  nsteps_ignore_context_core(m, t, reduced, t2);
}

lemma void nat_le_reflexive(nat n)
  requires true;
  ensures nat_le(n, n) == true;
{
  switch(n) {
    case zero:
    case succ(n0): nat_le_reflexive(n0);
  }
}

lemma void nat_le_succ(nat n)
  requires true;
  ensures nat_le(n, succ(n)) == true;
{
  switch(n) {
    case zero:
    case succ(n0): nat_le_succ(n0);
  }
}


lemma void nat_le_either(nat n, nat m) 
  requires true;
  ensures nat_le(n, m) || nat_le(m, n);
{
  switch(n) {
    case zero:
    case succ(n0):
      switch(m) {
        case zero:
        case succ(m0):
          nat_le_either(n0, m0);
      }
  }
}

lemma void nat_le_both(nat n1, nat n2)
  requires nat_le(n1, n2) && nat_le(n2, n1);
  ensures (n1 == n2);
{
  switch(n1) {
    case zero: switch(n2) {
      case zero:
      case succ(n2_):
    }
    case succ(n1_):
    switch(n2) {
      case zero:
      case succ(n2_):
        nat_le_both(n1_, n2_);
    }
  }
}






lemma void nat_le_not_eq(nat x, nat y)
  requires nat_le(x, y) == true &*& x != y;
  ensures nat_le(x, prev(y)) == true;
{
  assume(false);
}


lemma void nsteps_id(nat m, nat n, term t)
  requires step(nsteps(m, t)) == none &*& nat_le(m, n) == true;
  ensures nsteps(m, t) == nsteps(n, t);
{
  switch(n) {
    case zero:
      switch(m) {
        case zero:
        case succ(m0):
      }
    case succ(n0):
      switch(m) {
        case zero:
          nsteps_id(m, n0, t);
        case succ(m0):
          if(m0 != n0) {
            nat_le_not_eq(m, n);
            nsteps_id(m, n0, t);
          }
      }
  }
}

fixpoint boolean nat_le(nat n1, nat n2) {
  switch(n1) {
    case zero: return true;
    case succ(prev1):return 
    switch(n2) {
      case zero: return false;
      case succ(prev2): return nat_le(prev1, prev2);
    };
  }
}

lemma void nsteps_converges(nat n)
  requires exists<nat>(?m1) &*& exists<nat>(?m2) &*& step(nsteps(m1, ks(n))) == none &*& step(nsteps(m2, ks(n))) == none;
  ensures nsteps(m1, ks(n)) == nsteps(m2, ks(n));
{
  boolean le = nat_le(m1, m2);
  if(le) {
    nsteps_id(m1, m2, ks(n));
  } else {
    nat_le_either(m1, m2);
    nsteps_id(m2, m1, ks(n));
  }
}

lemma void ks_step_parity(nat n)
  requires true;
  ensures is_even(n) ? exists<nat>(?m) &*& nsteps(m, ks(n)) == K : exists(?m) &*& nsteps(m, ks(n)) == apply(K, K);
{
  switch(n) {
    case zero: 
      close exists(zero);
    case succ(n0):
      if(is_even(n)) {
        ks_step_parity(n0);
        nsteps_ignore_context(ks(n0), apply(K, K), K); 
        open exists(?m0);
        close exists(succ(m0));
      } else {
        ks_step_parity(n0);
        nsteps_ignore_context(ks(n0), K, K); 
        open exists(?m0);
        close exists(succ(m0));
      }
  }
}

fixpoint term nsteps(nat n, term t) {
  switch(n) {
    case zero: return t;
    case succ(n0): return switch(step(nsteps(n0, t))) {
      case none: return nsteps(n0, t);
      case some(reduced): return reduced;
    };
  }
}

fixpoint term reduce_ks(nat n) {
  switch(n) {
    case zero: return K;
    case succ(n0): 
      return switch(n0) {
        case zero: return apply(K, K);
        case succ(n00): return reduce_ks(n00); 
      };
  }
}

fixpoint int size(term t) {
  switch(t) {
    case K: return 1;
    case S: return 1;
    case apply(left, right): return size(left) + size(right) + 1;
  }
}

fixpoint boolean noS(term t) {
  switch(t) {
    case K: return true;
    case S: return false;
    case apply(left, right): return noS(left) && noS(right);
  }
}

fixpoint term ks(nat n) {
  switch(n) {
    case zero: return K;
    case succ(n0): return apply(ks(n0), K);
  }
}

lemma_auto(size(t)) void size_positive(term t) 
  requires true;
  ensures 0 < size(t);
{
  switch(t) {
    case K: 
    case S:
    case apply(t1, t2): size_positive(t1); size_positive(t2);
  }
}

lemma void step_preserves_noS(term t)
  requires noS(t) == true;
  ensures switch(step(t)) { case none: return true; case some(reduced): return noS(reduced) == true; };
{
  switch(t) {
    case K: 
    case S: 
    case apply(left, right):
      switch(left) {
        case K: switch(step(right)) {
          case none: 
          case some(reduced): step_preserves_noS(right); // rec
        };
        case S: 
        case apply(leftleft, leftright):
          switch(leftleft) {
            case K: 
              switch(step(leftright)) {
                case none: switch(step(right)) { 
                  case none: 
                  case some(reduced): step_preserves_noS(right); // rec
                };
                case some(reduced): step_preserves_noS(leftright); // rec
              };
            case S:
            case apply(leftleftleft, leftleftright):
              switch(leftleftleft) {
                case K: switch(step(leftleftright)) {
                    case none: switch(step(leftright)) {
                      case none: switch(step(right)) {
                        case none: 
                        case some(reduced): step_preserves_noS(right); 
                      };
                      case some(reduced): step_preserves_noS(leftright); // rec
                    };
                    case some(reduced): step_preserves_noS(leftleftright); // rec
                  };
                case S:
                case apply(leftleftleftleft, leftleftleftright): 
                  switch(step(left)) {
                    case none: switch(step(right)) {
                      case none: 
                      case some(reduced): step_preserves_noS(right); // rec
                      };
                    case some(reduced): step_preserves_noS(left);
                  };
              };
          };
      };
  }
}

lemma void step_with_noS_decreases_size(term t)
  requires noS(t) == true;
  ensures switch(step(t)) { case none: return true; case some(reduced): return size(reduced) < size(t); };
{
    switch(t) {
    case K: 
    case S: 
    case apply(left, right):
      switch(left) {
        case K: 
          switch(step(right)) {
            case none: 
            case some(reduced): step_with_noS_decreases_size(right);
          };
        case S: 
        case apply(leftleft, leftright):
          switch(leftleft) {
            case K: 
              switch(step(leftright)) {
                case none: switch(step(right)) { 
                  case none: some(leftright);
                  case some(reduced): step_with_noS_decreases_size(right);
                };
                case some(reduced): step_with_noS_decreases_size(leftright);
              };
            case S: switch(step(leftright)) {
                case none: switch(step(right)) { 
                  case none:  
                  case some(reduced): step_with_noS_decreases_size(right);
                };
                case some(reduced): step_with_noS_decreases_size(leftright);
              };
            case apply(leftleftleft, leftleftright):
              switch(leftleftleft) {
                case K: switch(step(leftleftright)) {
                    case none: switch(step(leftright)) {
                      case none: switch(step(right)) {
                        case none:                         
                        case some(reduced): step_with_noS_decreases_size(right);
                      };
                      case some(reduced): step_with_noS_decreases_size(leftright);
                    };
                    case some(reduced): step_with_noS_decreases_size(leftleftright);
                  };
                case S: 
                case apply(leftleftleftleft, leftleftleftright): 
                switch(step(left)) {
                    case none: switch(step(right)) {
                      case none: 
                      case some(reduced): step_with_noS_decreases_size(right); // rec
                      };
                    case some(reduced): step_with_noS_decreases_size(left);
                  };
              };
          };
      };
  }
}

/*lemma void nsteps_K(nat n)
  requires true;
  ensures nsteps(n, K) == K; 
{
  switch(n) {
    case zero:
    case succ(n0):
      nsteps_K(n0);
  }  
}*/
@*/

/*@ 
predicate term(Term t; term state) =
  t != null &*& [_]t.type |-> ?type &*& type == 1 || type == 2 || type == 3 &*&
  type == 1 ? 
    state == K 
    :
    (type == 2 ? 
      state == S
      :
      (t.left |-> ?first &*& t.right |-> ?second &*& first != null &*& second != null &*& [_]term(first, ?state1) &*& [_]term(second, ?state2) &*& state == apply(state1, state2)));

predicate exists<t>(t v) = true;
@*/

class Term {
  int type; // 1: K, 2: S, 3: apply
  Term left;
  Term right;
  
  Term(int type, Term left, Term right)
    //@ requires true;
    //@ ensures this.type |-> type &*& this.left |-> left &*& this.right |-> right;
  {
    this.type = type;
    this.left = left;
    this.right = right;
  }
  
  static Term createK()
    //@ requires true;
    //@ ensures result != null &*& term(result, K);
  {
    Term res = new Term(1, null, null);
    //@ close term(res, K);
    return res;
  }
  
  static Term createS()
    //@ requires true;
    //@ ensures result != null &*& term(result, S);
  {
    Term res = new Term(2, null, null);
    //@ close term(res, S);
    return res;
  }
  
  static Term createApply(Term left, Term right)
    //@ requires [_]term(left, ?state1) &*& [_]term(right, ?state2);
    //@ ensures result != null &*& [_]term(result, apply(state1, state2));
  {
    //@ open [?f1]term(left, state1);
    //@ close [f1]term(left, state1);
    //@ open [?f2]term(right, state2);
    //@ close [f2]term(right, state2);
    Term res = new Term(3, left, right);
    //@ close [1]term(res, apply(state1, state2));
    return res;
  }
  
  static Term do_step(Term t)
    //@ requires [_]term(t, ?state);
    //@ ensures result == null ? step(state) == none : [_]term(result, ?state2) &*& step(state) == some(state2);
  {
    if(t.type == 1) {
      return null;
    } else if(t.type == 2) {
      return null;
    } else { // (_, _)
      if(t.left.type == 1 || t.left.type == 2) {
        Term reduced = do_step(t.right);
        if(reduced == null) {
          return null;
        } else {
          return createApply(t.left, reduced);
        }
      } else { // ((_, _), _)
        if(t.left.left.type == 1) {
          Term reduced = do_step(t.left.right);
          if(reduced == null) {
            reduced = do_step(t.right);
            if(reduced == null) {
              return t.left.right;
            } else {
              return createApply(t.left, reduced);
            }
          } else {
            return createApply(createApply(t.left.left, reduced), t.right);
          }
        } else if(t.left.left.type == 2) {
          Term reduced = do_step(t.left.right);
          if(reduced == null) {
            reduced = do_step(t.right);
            if(reduced == null) {
              return null;
            } else {
              return createApply(createApply(t.left.left, t.left.right), reduced);
            }
          } else {
            return createApply(createApply(t.left.left, reduced), t.right);
          }
        } else { // (((_, _), _), _)
          if(t.left.left.left.type == 1) {
            Term reduced = do_step(t.left);
            if(reduced == null) {
               reduced = do_step(t.right);
               if(reduced == null) {
                 return null;
               } else {
                 return createApply(t.left, reduced);
               }
            } else {
              return createApply(reduced, t.right);
            }
          } else if(t.left.left.left.type == 2) {
             Term reduced = do_step(t.left.left.right);
             if(reduced == null) {
               reduced = do_step(t.left.right);
               if(reduced == null) {
                 reduced = do_step(t.right);
                 if(reduced == null) {
                   return createApply(createApply(t.left.left.right, t.right), createApply(t.left.right, t.right));
                 } else {
                   return createApply(t.left, reduced);
                 }
               } else {
                  return createApply(createApply(createApply(t.left.left.left, t.left.left.right), reduced), t.right);
               }
             } else {
               return createApply(createApply(createApply(t.left.left.left, reduced), t.left.right), t.right);
             }
          } else { // ((((_, _), _), _))
            Term reduced = do_step(t.left);
            if(reduced == null) {
               reduced = do_step(t.right);
               if(reduced == null) {
                 return null;
               } else {
                 return createApply(t.left, reduced);
               }
            } else {
              return createApply(reduced, t.right);
            }
          }
        }
      }
    }
  }
  
  static Term reduction(Term t)
    //@ requires [_]term(t, ?state);
    //@ ensures [_]term(result, ?state2) &*& exists(?n) &*& nsteps(n, state) == state2 &*& step(state2) == none;
  {
    //@ nat count = zero;
    Term curr = t;
    while(true) 
      //@ invariant [_]term(curr, ?state2) &*& nsteps(count, state) == state2;
    {
      Term newCur = do_step(curr);
      if(newCur == null) { 
        return curr;
        //@ close exists(count);
      }
      //@ count = succ(count); 
      curr = newCur;
    }
  }
  
  static Term reduction_terminating(Term t)
    //@ requires [_]term(t, ?state) &*& noS(state) == true;
    //@ ensures [_]term(result, ?state2) &*& exists(?n) &*& nsteps(n, state) == state2 &*& step(state2) == none;
  {
    //@ nat count = zero;
    Term curr = t;
    while(true) 
      //@ invariant [_]term(curr, ?state2) &*& noS(state2) == true &*& nsteps(count, state) == state2;
      //@ decreases size(state2);
    {
      Term newCur = do_step(curr);
      if(newCur == null) { 
        return curr;
        //@ close exists(count);
      }
      //@ count = succ(count); 
      curr = newCur;
      //@ step_preserves_noS(state2);
      //@ step_with_noS_decreases_size(state2);
    }
  }
  
  static void test_parity(Term t) 
    //@ requires exists<nat>(?n) &*& term(t, ks(n));
    //@ ensures true;
  {
    Term reduced = reduction(t);
    //@ assert [_]term(reduced, ?reducedstate);
    //@ ks_step_parity(n);
    //@ nsteps_converges(n);
    /*@
    if(is_even(n)) {
      assert reducedstate == K;
    } else {
      assert reducedstate == apply(K, K);
    }
    @*/
  }
}