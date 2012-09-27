//@ #include "listex2.gh"

/*@

    //TODO: move general lemma's to list.h or listex.h 

lemma void mem_snoc<t>(t v1, list<t> vs, t v2) 
    requires true;
    ensures mem(v1, snoc(vs, v2)) == (mem(v1, vs) || v1 == v2);
{
    mem_append(v1, vs, cons(v2, nil));
}


lemma void distinct_snoc<t>(list<t> l, t v)
    requires distinct(l) == true &*& !mem(v, l);
    ensures distinct(snoc(l, v)) == true;
{
    switch(l) {
        case nil:
        case cons(h, t):
           mem_snoc(h, t, v);
           distinct_snoc(t, v);
    }
}

lemma void nth_tail<t>(int i, list<t> l) 
  requires i > 0;
  ensures nth(i-1, tail(l)) == nth(i,l);
{
    switch (l) {
      case nil: 
      case cons(x0, xs0): 
    }
}
  
lemma void length_tail<t>(list<t> l) 
  requires length(l) > 0;
  ensures length(tail(l)) == length (l) - 1;
{
    switch (l) {
      case nil: 
      case cons(x0, xs0): 
    }
}

lemma void nth_snoc_length<t>(list<t> l, t el)
    requires true;
    ensures nth(length(l), snoc(l, el)) == el;
{
    switch (l) {
      case nil: 
      case cons(x0, xs0): 
        nth_snoc_length(xs0, el);
    }
}

lemma void remove_all1_mem<t>(t v, t v2, list<t> l)
    requires true;
    ensures mem(v, remove_all1(v2, l)) == (v != v2 && mem(v, l));
{
    switch(l) {
        case nil:
        case cons(h, t): remove_all1_mem(v, v2, t);
    }
}
lemma void remove_all1_id<t>(t v, list<t> l)
    requires !mem(v, l);
    ensures remove_all1(v, l) == l;
{
    switch(l) {
        case nil:
        case cons(h, t): remove_all1_id(v, t);
    }
}

@*/
