/*
fixpoint int fact(int x)
  decreases x;
{
  return x == 0 ? 1 : x * fact(x - 1);
}
*/
/*@
// approximations

fixpoint int fact_approx_0(int x) { return x == 0 ? 1 : 42; /* any value */ }
fixpoint int fact_approx_1(int x) { return x == 0 ? 1 : x * fact_approx_0(x - 1); }
fixpoint int fact_approx_2(int x) { return x == 0 ? 1 : x * fact_approx_1(x - 1); }
// ...
fixpoint int fact_approx_n(int x); // {...}
fixpoint int fact_approx_nplus1(int x) { return x == 0 ? 1 : x * fact_approx_n(x - 1); }

// fact_step(fact_n) = fact_nplus1
fixpoint int fact_step(fixpoint(int x, int r) fact_n, int x) { return x == 0 ? 1 : x * fact_n(x - 1); }

fixpoint T id<T>(T a) { return a; }
fixpoint int fact(int x) { return fix(fact_step, id, x); }

lemma void fact_def(int x)
  requires 0 <= x;
  ensures fact(x) == (x == 0 ? 1 : x * fact(x - 1));
{
  if(fact(x) != (x == 0 ? 1 : x * fact(x - 1))) {
    fix_unfold(fact_step, id, x);
  }
}
@*/