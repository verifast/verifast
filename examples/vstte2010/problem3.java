class Node {
    int head;
    Node next;
}

/*@

predicate List(Node n; list<int> elems) =
    n == null ?
        elems == nil
    :
        n.head |-> ?head &*&
        n.next |-> ?next &*&
        List(next, ?tail) &*&
        elems == cons(head, tail);

predicate Lseg(Node f, Node l; list<int> elems) =
    f == l ?
        elems == nil
    :
        f.head |-> ?head &*&
        f.next |-> ?next &*&
        Lseg(next, l, ?elems0) &*&
        elems == cons(head, elems0);

lemma void Lseg_add(Node ll)
    requires Lseg(ll, ?jj, ?elems0) &*& jj.head |-> ?head &*& jj.next |-> ?next &*& List(next, ?elems1);
    ensures Lseg(ll, next, append(elems0, cons(head, nil))) &*& List(next, elems1);
{
    open Lseg(ll, jj, elems0);
    if (ll == jj) {
        open List(next, elems1);
    } else {
        open List(next, elems1);
        Lseg_add(ll.next);
    }
}

fixpoint int find<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x0, xs0): return x0 == x ? 0 : 1 + find(x, xs0);
    }
}

lemma void Lseg_to_List(Node ll)
    requires Lseg(ll, ?jj, ?elems0) &*& List(jj, ?elems1);
    ensures List(ll, append(elems0, elems1));
{
    open Lseg(ll, jj, elems0);
    if (ll != jj) {
        Lseg_to_List(ll.next);
    }
}

@*/

class Problem3 {

    public static int findFirstZero(Node ll)
        //@ requires List(ll, ?elems);
        //@ ensures List(ll, elems) &*& result == find(0, elems);
    {
        Node jj = ll;
        int i = 0;
        while (jj != null && jj.head != 0)
            /*@
            invariant
                Lseg(ll, jj, ?elems0) &*& List(jj, ?elems1) &*& elems == append(elems0, elems1) &*&
                find(0, elems) == i + find(0, elems1);
            @*/
        {
            //@ append_assoc(elems0, cons(jj.head, nil), tail(elems1));
            jj = jj.next;
            i++;
            //@ Lseg_add(ll);
        }
        //@ open List(null, _);
        //@ Lseg_to_List(ll);
        return i;
    }
}