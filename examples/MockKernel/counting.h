#ifndef COUNTING_H
#define COUNTING_H

/*@

predicate_family countable(void * countable)(predicate() p);

typedef lemma void countable();
    requires countable(this)(?p) &*& [?f1]p() &*& [?f2]p();
    ensures [f1 + f2]p() &*& f1 + f2 <= 1;

predicate counted(predicate() p, int count);
predicate ticket(predicate() p, real frac);

lemma void create_counted(predicate() p);
    requires p() &*& countable(?countable)(p) &*& is_countable(countable);
    ensures counted(p, 0);

lemma void counted_create_ticket(predicate() p);
    requires counted(p, ?count);
    ensures counted(p, count + 1) &*& ticket(p, ?f) &*& [f]p();

lemma void counted_ticket_dispose(predicate() p);
    requires counted(p, ?count) &*& ticket(p, ?f) &*& [f]p();
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

/*@

predicate counted_ghost_cell_factory(predicate(void *, int) p, void *a, int count);
predicate counted_ghost_cell<t>(predicate(void *, int) p, void *a, int index; int count, t value);
predicate counted_ghost_cell_ticket<t>(predicate(void *, int) p, void *a, int index; t value);

lemma void create_counted_ghost_cell_factory(predicate(void *, int) p, void *a);
    requires countable_integer(?lem)(p) &*& is_countable_integer(lem) &*& p(a, _);
    ensures counted_ghost_cell_factory(p, a, 0);

lemma void counted_ghost_cell_factory_create_cell<t>(predicate(void *, int) p, void *a, t value);
    requires counted_ghost_cell_factory(p, a, ?count);
    ensures counted_ghost_cell_factory(p, a, count + 1) &*& counted_ghost_cell(p, a, count, 0, value);

lemma void counted_ghost_cell_create_ticket<t>(predicate(void *, int) p, void *a, int index);
    requires counted_ghost_cell<t>(p, a, index, ?count, ?value);
    ensures counted_ghost_cell<t>(p, a, index, count + 1, value) &*& [2]counted_ghost_cell_ticket<t>(p, a, index, value);

lemma void counted_ghost_cell_ticket_dispose<t>(predicate(void *, int) p, void *a, int index);
    requires counted_ghost_cell<t>(p, a, index, ?count, ?value) &*& [2]counted_ghost_cell_ticket<t>(p, a, index, ?value2);
    ensures counted_ghost_cell<t>(p, a, index, count - 1, value) &*& 1 <= count &*& value2 == value;

lemma void counted_ghost_cell_dispose<t>(predicate(void *, int) p, void *a);
    requires counted_ghost_cell_factory(p, a, ?count) &*& 0 < count &*& counted_ghost_cell<t>(p, a, count - 1, 0, _);
    ensures counted_ghost_cell_factory(p, a, count - 1);

lemma void counted_ghost_cell_factory_dispose(predicate(void *, int) p, void *a);
    requires counted_ghost_cell_factory(p, a, 0);
    ensures p(a, _);

@*/

#endif