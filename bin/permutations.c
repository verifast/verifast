//@ #include "permutations.gh"
//@ #include "listex.gh"
//@ #include "nat.gh"

/*@
lemma_auto void is_permutation_reflexive(list<int> xs) 
  requires true;
  ensures is_permutation(xs, xs) == true;
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      switch(t) {
        case nil:
        case cons(h0, t0):
          is_permutation_reflexive(t);
      }
  }
}

lemma void not_mem_remove<t>(list<t> xs, t x, t y)
  requires ! mem(x, remove(y, xs)) && x != y;
  ensures ! mem(x, xs);
{
  switch(xs) {
    case nil:
    case cons(h, t):
     if(h == x) {
     } else {
      if(h == y) {
      } else {
        not_mem_remove(t, x, y);
      }
     }
  }
}

lemma void is_perm_remove<t>(list<t> xs, list<t> ys, t x)
  requires is_permutation(xs, ys) == true;
  ensures is_permutation(remove(x, xs), remove(x, ys)) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(x == h) {
      } else {
        neq_mem_remove(h, x, ys);
        remove_commutes(ys, h, x);
        is_perm_remove(t, remove(h, ys), x);  
      }
  }
}

lemma void is_perm_mem<t>(list<t> xs, list<t> ys, t x) 
  requires is_permutation(xs, ys) == true;
  ensures mem(x, xs) == mem(x, ys);
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(h == x) {
      } else {
         switch(ys) {
           case nil:
           case cons(h0, t0):
             is_perm_mem(t, remove(h, ys), x);
             if(mem(x, t)) {
               mem_remove_mem(x, h, ys);
             } else {
               not_mem_remove(ys, x, h);
             }
         }
      }
  }
}

lemma void is_perm_transitive<t>(list<t> xs, list<t> ys, list<t> zs)
  requires is_permutation(xs, ys) == true &*& is_permutation(ys, zs)== true;
  ensures is_permutation(xs, zs) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      is_perm_mem(ys, zs, h);
      is_perm_remove(ys, zs, h);
      is_perm_transitive(t, remove(h, ys), remove(h, zs));
  }
}

lemma void is_perm_cons_remove<t>(list<t> xs, t x)
  requires mem(x, xs) == true;
  ensures is_permutation(xs, cons(x, remove(x, xs))) == true;
{
  switch(xs) {
    case nil:
    case cons(h, t):
      if(h != x) {
        is_perm_cons_remove(t, x);
      }
  }
}

lemma void is_perm_symmetric_core<t>(nat n, list<t> xs, list<t> ys)
  requires is_permutation(xs, ys) == true &*& length(xs) == int_of_nat(n);
  ensures is_permutation(ys, xs) == true;
{
  switch(n) {
    case zero:
      switch(xs) { case nil: case cons(hx, tx): }
      switch(ys) { case nil: case cons(hy, ty): }
    case succ(n0):
     switch(xs) {
       case nil: switch(ys) { case nil: case cons(hy, ty): }
       case cons(hx, tx):
         switch(ys) {
           case nil:
           case cons(hy, ty):
             is_perm_symmetric_core(n0, tx, remove(hx, ys));
             if(hx == hy) {
             } else {
               is_perm_cons_remove(ys, hx);
               is_perm_transitive(ys, cons(hx, remove(hx, ys)), xs);
             }
         }
     }
  }
}

lemma void is_perm_symmetric<t>(list<t> xs, list<t> ys)
  requires is_permutation(xs, ys) == true;
  ensures is_permutation(ys, xs) == true;
{
  is_perm_symmetric_core(nat_of_int(length(xs)), xs, ys); 
}

@*/