#ifndef LISTS_H
#define LISTS_H

/*@

predicate lseg(void *first, void *last, list<void *> xs, predicate(void *) p) =
    first == last ?
        xs == nil
    :
        pointer(first, ?next) &*& lseg(next, last, ?xs0, p) &*& xs == cons(first, xs0) &*& p(first);

lemma void lseg_separate(void *first, void *element);
    requires lseg(first, ?last, ?xs, ?p) &*& mem(element, xs) == true;
    ensures
        lseg(first, element, ?xs1, p) &*& pointer(element, ?next) &*& p(element) &*& lseg(next, last, ?xs2, p) &*&
        xs == append(xs1, cons(element, xs2));

lemma void lseg_append(void *n1);
    requires lseg(n1, ?n2, ?xs0, ?p) &*& lseg(n2, ?n3, ?xs1, p) &*& lseg(n3, 0, ?xs2, p);
    ensures lseg(n1, n3, append(xs0, xs1), p) &*& lseg(n3, 0, xs2, p);

lemma void lseg_append_final(void *n1);
    requires lseg(n1, ?n2, ?xs0, ?p) &*& lseg(n2, 0, ?xs1, p);
    ensures lseg(n1, 0, append(xs0, xs1), p);

lemma void lseg_add(void *n1);
    requires lseg(n1, ?n2, ?xs0, ?p) &*& pointer(n2, ?n3) &*& p(n2) &*& lseg(n3, 0, ?xs1, p);
    ensures lseg(n1, n3, append(xs0, cons(n2, nil)), p) &*& lseg(n3, 0, xs1, p) &*& append(xs0, cons(n2, xs1)) == append(append(xs0, cons(n2, nil)), xs1);

@*/

void linked_list_remove(void *phead, void *element);
    //@ requires pointer(phead, ?head) &*& lseg(head, 0, ?xs, ?p) &*& mem(element, xs) == true;
    //@ ensures pointer(phead, ?head1) &*& lseg(head1, 0, remove(element, xs), p) &*& pointer(element, _) &*& p(element);

#endif