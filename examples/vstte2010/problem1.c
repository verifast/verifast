/* verifies with prover Z3 with overflow checking disabled */

//@ #include "listex.gh"
//@ #include "arrays.gh"

/*@
fixpoint bool le(unit u, int x, int y) {
    switch (u) {
        case unit: return x <= y;
    }
}

fixpoint int max_func(unit u, int x, int y) {
    switch (u) {
        case unit: return x < y ? y : x;
    }
}

fixpoint int plus(unit u, int x, int y) {
    switch (u) {
        case unit: return x + y;
    }
}

lemma void le_mult_compat(int x, int y1, int y2)
    requires 0 <= x &*& y1 <= y2;
    ensures x * y1 <= x * y2;
{
  int i = x;
  while(0 < i) 
    invariant 0 <= i &*& i <= x &*& x * y1 - i * y1 <= x * y2 - i * y2;
    decreases i;
  {
    i = i - 1;
  }
}

lemma void mult_congr_l(int x1, int x2, int y)
    requires x1 == x2;
    ensures x1 * y == x2 * y;
{
  if(0 <= y) {
    int i = y;
    while(0 < i)
      invariant 0 <= i &*& i <= y &*& x1 * y - x1 * i == x2 * y - x2 * i;
      decreases i;
    {
      i = i - 1;
    }
  } else {
    int i = y;
    while(i < 0)
      invariant y <= i &*& i <= 0 &*& x1 * y - x1 * i == x2 * y - x2 * i;
      decreases -i;
    {
      i = i + 1;
    }
  }
}
@*/

void problem1(int *a, int N)
   //@ requires ints(a, N, ?elems) &*& forall(elems, (le)(unit, 0)) == true;
   //@ ensures ints(a, N, elems);
{
    int sum = 0;
    int max = 0;
    int i = 0;
    for (; i < N; i++)
        /*@
        invariant
            a[0..N] |-> elems &*&
            0 <= i &*& i <= N &*&
            0 <= max &*&
            sum == fold_left(0, (plus)(unit), take(i, elems)) &*&
            max == fold_left(0, (max_func)(unit), take(i, elems)) &*&
            sum <= i * max;
        @*/
    {
        int x = a[i];
        int oldMax = max;
        if (max < x) {
            max = x;
        }
        //@ le_mult_compat(i, oldMax, max);
        sum += a[i];
        //@ take_plus_one(i, elems);
        //@ fold_left_append(0, (plus)(unit), take(i, elems), cons(x, nil));
        //@ fold_left_append(0, (max_func)(unit), take(i, elems), cons(x, nil));
    }
    //@ mult_congr_l(i, N, max);
    assert(sum <= N * max);
}
