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
                  case some(reduced): return some(apply(apply(S, leftright), right)); // rec
                };
                case some(reduced): return some(apply(apply(S, reduced), right)); // rec
              };
            case apply(leftleftleft, leftleftright):
              return switch(leftleftleft) {
                case K: return switch(step(leftleftright)) {
                    case none: return switch(step(leftright)) {
                      case none: return switch(step(right)) {
                        case none: return none;
                        case some(reduced): return some(apply(apply(apply(K, leftleftright), leftright), reduced)); // rec
                      };
                      case some(reduced): return some(apply(apply(apply(K, leftleftright), reduced), right)); // rec
                    };
                    case some(reduced): return some(apply(apply(apply(K, reduced), leftright), right)); // rec
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
                case apply(leftleftleftleft, leftleftleftright): return switch(step(leftleftleft)) {
                  case none: return switch(step(leftleftright)) {
                    case none: return switch(step(leftright)) {
                      case none: return switch(step(right)) {
                        case none: return none;
                        case some(reduced): return some(apply(apply(apply(leftleftleft, leftleftright), leftright), reduced)); // rec
                      };
                      case some(reduced): return some(apply(apply(apply(leftleftleft, leftleftright), reduced), right)); // rec
                    };
                    case some(reduced): return some(apply(apply(apply(leftleftleft, reduced), leftright), right)); // rec
                  };
                  case some(reduced): return some(apply(apply(apply(reduced, leftleftright), leftright), right)); // rec
                }; 
              };
          };
      };
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
  assume(false);
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
          switch(step(right)) {
            case none: 
            case some(reduced): step_with_noS_decreases_size(right);
          };
        case apply(leftleft, leftright):
          switch(leftleft) {
            case K: 
              switch(step(leftright)) {
                case none: switch(step(right)) { 
                  case none: some(leftright); // step
                  case some(reduced): step_with_noS_decreases_size(right); // rec
                };
                case some(reduced): step_with_noS_decreases_size(leftright); // rec
              };
            case S: switch(step(leftright)) {
                case none: switch(step(right)) { 
                  case none:  
                  case some(reduced): step_with_noS_decreases_size(right); // rec
                };
                case some(reduced): step_with_noS_decreases_size(leftright); // rec
              };
            case apply(leftleftleft, leftleftright):
              switch(leftleftleft) {
                case K: switch(step(leftleftright)) {
                    case none: switch(step(leftright)) {
                      case none: switch(step(right)) {
                        case none:                         
                        case some(reduced):  // rec
                      };
                      case some(reduced): return some(apply(apply(apply(K, leftleftright), reduced), right)); // rec
                    };
                    case some(reduced): return some(apply(apply(apply(K, reduced), leftright), right)); // rec
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
                case apply(leftleftleftleft, leftleftleftright): return switch(step(leftleftleft)) {
                  case none: return switch(step(leftleftright)) {
                    case none: return switch(step(leftright)) {
                      case none: return switch(step(right)) {
                        case none: return none;
                        case some(reduced): return some(apply(apply(apply(leftleftleft, leftleftright), leftright), reduced)); // rec
                      };
                      case some(reduced): return some(apply(apply(apply(leftleftleft, leftleftright), reduced), right)); // rec
                    };
                    case some(reduced): return some(apply(apply(apply(leftleftleft, reduced), leftright), right)); // rec
                  };
                  case some(reduced): return some(apply(apply(apply(reduced, leftleftright), leftright), right)); // rec
                }; 
              };
          };
      };
  }
}
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
      (t.left |-> ?first &*& t.right |-> ?second &*& [_]term(first, ?state1) &*& [_]term(second, ?state2) &*& state == apply(state1, state2)));

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
      //@ assume(false);
        if(t.left.left.type == 2) {
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
        } else {
          
        }
      }
    }
  }
  
  static Term reduction(Term t)
    //@ requires [_]term(t, ?state);
    //@ ensures [_]term(result, ?state2) &*& exists(?n) &*& nsteps(n, state) == state2;
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
    //@ ensures [_]term(result, ?state2) &*& exists(?n) &*& nsteps(n, state) == state2;
  {
    //@ nat count = zero;
    Term curr = t;
    while(true) 
      //@ invariant [_]term(curr, ?state2) &*& noS(state2) == true &*& nsteps(count, state) == state2;
    {
      Term newCur = do_step(curr);
      if(newCur == null) { 
        return curr;
        //@ close exists(count);
      }
      //@ count = succ(count); 
      curr = newCur;
      //@ step_preserves_noS(state2);
    }
  }
}