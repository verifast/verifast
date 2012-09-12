//@ #include "wfmap.gh"

/*@


lemma void wfmap_contains_contains_key<t,tk>(list<t> s, fixpoint(t, tk) fk, t el)
    requires is_wfmap(s, fk) == true;
    ensures wfmap_contains(s, el) == (wfmap_contains_key(s, fk, fk(el)) && wfmap_get(s, fk, fk(el)) == el);
{
    switch(s) {
        case nil:
        case cons(sh, st):
            wfmap_contains_contains_key(st, fk, el);
    }
}

lemma void wfmap_contains_equal<t,tk>(list<t> s, fixpoint(t, tk) fk, t el, t el2)
    requires is_wfmap(s, fk) == true &*& wfmap_contains(s, el) == true &*& wfmap_contains(s, el2) == true &*& fk(el) == fk(el2);
    ensures el == el2;
{
    switch(s) {
        case nil:
        case cons(sh, st):
           if(sh == el || sh == el2) {
               wfmap_contains_contains_key(st, fk, el);
               wfmap_contains_contains_key(st, fk, el2);
           } else {
               wfmap_contains_equal(st, fk, el, el2);
           }
    }
}

@*/
