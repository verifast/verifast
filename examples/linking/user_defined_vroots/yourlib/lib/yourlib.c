//@ #include "yourlib.gh"

/*@
lemma void length_not_zero_not_nil<t>(list<t> xs)
     requires length(xs) != 0;
     ensures xs != nil;
{
     switch (xs) {
         case nil:
           assert false;
         case cons(x0, xs0):
     }
}
@*/
