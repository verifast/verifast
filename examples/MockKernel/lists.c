#include "stdlib.h"
#include "stdbool.h"
#include "lists.h"

/*@

lemma void lseg_append(void *n1)
    requires lseg(n1, ?n2, ?xs0, ?p) &*& lseg(n2, ?n3, ?xs1, p) &*& lseg(n3, 0, ?xs2, p);
    ensures lseg(n1, n3, append(xs0, xs1), p) &*& lseg(n3, 0, xs2, p);
{
    open lseg(n1, n2, xs0, p);
    if (n1 == n2) {
    } else {
        assert pointer(n1, ?n1Next);
        lseg_append(n1Next);
        if (n3 != 0) {
            open lseg(n3, 0, xs2, p);
            pointer_distinct(n1, n3);
            close lseg(n3, 0, xs2, p);
        }
        close lseg(n1, n3, append(xs0, xs1), p);
    }
}

lemma void lseg_append_final(void *n1)
    requires lseg(n1, ?n2, ?xs0, ?p) &*& lseg(n2, 0, ?xs1, p);
    ensures lseg(n1, 0, append(xs0, xs1), p);
{
    close lseg(0, 0, nil, p);
    lseg_append(n1);
    open lseg(0, 0, nil, p);
}

lemma void lseg_add(void *n1)
    requires lseg(n1, ?n2, ?xs0, ?p) &*& pointer(n2, ?n3) &*& p(n2) &*& lseg(n3, 0, ?xs1, p);
    ensures lseg(n1, n3, append(xs0, cons(n2, nil)), p) &*& lseg(n3, 0, xs1, p) &*& append(xs0, cons(n2, xs1)) == append(append(xs0, cons(n2, nil)), xs1);
{
    open lseg(n3, 0, xs1, p);
    close lseg(n3, n3, nil, p);
    if (n3 != 0) pointer_distinct(n2, n3);
    close lseg(n2, n3, cons(n2, nil), p);
    close lseg(n3, 0, xs1, p);
    lseg_append(n1);
    append_assoc(xs0, cons(n2, nil), xs1);
}

@*/

void linked_list_remove(void *phead, void *element)
    //@ requires pointer(phead, ?head) &*& lseg(head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures pointer(phead, ?head1) &*& lseg(head1, 0, remove(element, xs), p) &*& pointer(element, _) &*& p(element);
{
    void **pnext = phead;
    while (*pnext != element)
        /*@
        invariant
            pointer(phead, head) &*&
            pnext == phead ?
                lseg(head, 0, xs, p)
            :
                lseg(head, pnext, ?xs0, p) &*& pointer(pnext, ?next) &*& p(pnext) &*& lseg(next, 0, ?xs1, p) &*&
                append(xs0, cons(pnext, xs1)) == xs &*&
                mem(element, xs1) == true &*&
                remove(element, xs) == append(xs0, cons(pnext, remove(element, xs1)));
        @*/
    {
        void **next = *pnext;
        /*@
        if (pnext == phead) {
            open lseg(head, 0, xs, p);
            pointer_distinct(phead, head);
            close lseg(head, head, nil, p);
        } else {
            assert lseg(head, pnext, ?xs0, p);
            close lseg(next, next, nil, p);
            open lseg(next, 0, ?xs1, p);
            pointer_distinct(pnext, next);
            close lseg(next, 0, xs1, p);
            close lseg(pnext, next, cons(pnext, nil), p);
            lseg_append(head);
            open lseg(next, 0, xs1, p);
            pointer_distinct(phead, next);
            append_assoc(xs0, cons(pnext, nil), xs1);
            append_assoc(xs0, cons(pnext, nil), remove(element, xs1));
        }
        @*/
        pnext = next;
    }
    //@ void *next = *pnext;
    //@ open lseg(next, 0, _, p);
    {
        void *nextNext = *((void **)*pnext);
        //@ assert lseg(nextNext, 0, ?xs2, p);
        *pnext = nextNext;
        /*@
        if (pnext != phead) {
            close lseg(pnext, 0, cons(pnext, xs2), p);
            lseg_append_final(head);
        }
        @*/
    }
}
