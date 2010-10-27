#ifndef COUNTING_EX_H
#define COUNTING_EX_H

/*@

predicate_family countable(void * countable)(predicate() p);

typedef lemma void countable();
    requires countable(this)(?p) &*& [?f1]p() &*& [?f2]p();
    ensures [f1 + f2]p() &*& f1 + f2 <= 1;

predicate counted(predicate() p, int count);
predicate counted_ticket(predicate() p, real frac);

lemma void create_counted(predicate() p);
    requires p() &*& countable(?countable)(p) &*& is_countable(countable);
    ensures counted(p, 0);

lemma void counted_create_ticket(predicate() p);
    requires counted(p, ?count);
    ensures counted(p, count + 1) &*& counted_ticket(p, ?f) &*& [f]p();

lemma void counted_ticket_dispose(predicate() p);
    requires counted(p, ?count) &*& counted_ticket(p, ?f) &*& [f]p();
    ensures counted(p, count - 1) &*& 0 < count;

lemma void counted_dispose(predicate() p);
    requires counted(p, 0);
    ensures p();

@*/

#endif