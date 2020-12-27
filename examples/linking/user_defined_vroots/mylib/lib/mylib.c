//@ #include "mylib.gh"

/*@
lemma void length_zero_eq_nil<t>(list<t> xs)
     requires length(xs) == 0;
     ensures xs == nil;
{
     switch (xs) {
         case nil:
         case cons(x0, xs0):
             assert false;
     }
}
@*/
