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

/*@

predicate_family countable_integer(void *lem)(predicate(void *, int) p);

typedef lemma void countable_integer();
    requires countable_integer(this)(?p) &*& [?f1]p(?a, ?v1) &*& [?f2]p(a, ?v2);
    ensures [f1 + f2]p(a, v1) &*& v2 == v1 &*& f1 + f2 <= 1;

predicate counted_integer(predicate(void *, int) p, void *a, int value, int count);
predicate counted_integer_ticket(predicate(void *, int) p, void *a, real frac);

lemma void create_counted_integer(predicate(void *, int) p, void *a);
    requires p(a, ?value) &*& countable_integer(?lem)(p) &*& is_countable_integer(lem);
    ensures counted_integer(p, a, value, 0);

lemma void counted_integer_create_ticket(predicate(void *, int) p, void *a);
    requires counted_integer(p, a, ?value, ?count);
    ensures counted_integer(p, a, value, count + 1) &*& counted_integer_ticket(p, a, ?f) &*& [f]p(a, value);

lemma void counted_integer_ticket_dispose(predicate(void *, int) p, void *a);
    requires counted_integer(p, a, ?value, ?count) &*& counted_integer_ticket(p, a, ?f) &*& [f]p(a, ?value1);
    ensures counted_integer(p, a, value, count - 1) &*& 1 <= count &*& value1 == value;

lemma void counted_integer_dispose(predicate(void *, int) p, void *a);
    requires counted_integer(p, a, ?value, 0);
    ensures p(a, value);

lemma void counted_integer_match_fraction(predicate(void *, int) p, void *a);
    requires counted_integer(p, a, ?value1, ?count) &*& [?f]p(a, ?value2);
    ensures counted_integer(p, a, value1, count) &*& [f]p(a, value1) &*& value2 == value1;

@*/

#endif