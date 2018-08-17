#ifndef TSO_H
#define TSO_H

/*@

predicate tso<a>(int id, predicate(a) p, fixpoint(a, a, bool) le, list<fixpoint(list<vararg>, a, a)> fs, a a;);

typedef lemma void le_refl<a>(fixpoint(a, a, bool) le)(a a);
    requires true;
    ensures le(a, a) == true;

typedef lemma void le_trans<a>(fixpoint(a, a, bool) le)(a a1, a a2, a a3);
    requires le(a1, a2) && le(a2, a3);
    ensures le(a1, a3) == true;

lemma int create_tso<a>(predicate(a) p, fixpoint(a, a, bool) le, list<fixpoint(list<vararg>, a, a)> fs, a a0);
    requires is_le_refl(_, le) &*& is_le_trans(_, le) &*& p(a0);
    ensures tso<a>(result, p, le, fs, a0);

lemma void tso_merge<a>();
    requires [?f1]tso<a>(?id, ?p, ?le, ?fs, ?a1) &*& [?f2]tso<a>(id, p, le, fs, ?a2);
    ensures [f1 + f2]tso(id, p, le, fs, ?a) &*& le(a1, a) == true &*& le(a2, a) == true;

lemma void tso_destroy<a>();
    requires tso<a>(?id, ?p, ?le, ?fs, ?a0);
    ensures p(?a1) &*& le(a0, a1) == true;

lemma void tso_weaken<a>(a a0);
    requires [?f]tso(?id, ?p, ?le, ?fs, ?a) &*& le(a0, a) == true;
    ensures [f]tso(id, p, le, fs, a0);

@*/

/*@

typedef lemma void tso_write_op(void **pp, void *v, predicate() pre, predicate() post)();
    requires pre() &*& *pp |-> _;
    ensures post() &*& *pp |-> v;

typedef lemma void tso_write_ctxt<a>(void **pp, void *v, predicate(a) p, fixpoint(a, a, bool) le, a p0, fixpoint(a, a) f, predicate() P, predicate() Q)(a p1, a p2);
    requires P() &*& le(p0, p1) == true &*& le(p1, p2) == true &*& p(p2) &*& is_tso_write_op(?op, pp, v, ?pre, ?post) &*& pre();
    ensures Q() &*& p(f(p2)) &*& le(p2, f(p2)) == true &*& le(f(p1), f(p2)) == true &*& post() &*& is_tso_write_op(op, pp, v, pre, post);

@*/

void tso_write/*@ <a> @*/(void **pp, void *v, int fid, ...);
    //@ requires [?frac]tso<a>(?id, ?p, ?le, ?fs, ?a0) &*& is_tso_write_ctxt(?ctxt, pp, v, p, le, a0, (nth(fid, fs))(varargs), ?P, ?Q) &*& P();
    //@ ensures [frac]tso<a>(id, p, le, fs, (nth(fid, fs))(varargs, a0)) &*& Q();

/*@

typedef lemma void tso_noop_body<a>(predicate(a) p, fixpoint(a, a, bool) le, a p0, fixpoint(a, a) f, predicate() P, predicate() Q)(a p1, a p2);
    requires P() &*& le(p0, p1) == true &*& le(p1, p2) == true &*& p(p2);
    ensures Q() &*& p(f(p2)) &*& le(p2, f(p2)) == true &*& le(f(p1), f(p2)) == true;

@*/

void tso_noop/*@ <a> @*/(int fid, ...);
    //@ requires [?frac]tso<a>(?id, ?p, ?le, ?fs, ?a0) &*& is_tso_noop_body(?body, p, le, a0, (nth(fid, fs))(varargs), ?P, ?Q) &*& P();
    //@ ensures [frac]tso<a>(id, p, le, fs, (nth(fid, fs))(varargs, a0)) &*& Q();

typedef long long prophecy_id;

/*@

predicate tso_prophecy(prophecy_id id, void *v);

@*/

prophecy_id create_tso_prophecy();
    //@ requires true;
    //@ ensures tso_prophecy(result, _);

/*@

typedef lemma void tso_read_op(void **pp, void *v, predicate() pre, predicate() post)();
    requires pre() &*& *pp |-> ?v1;
    ensures post() &*& *pp |-> v1 &*& v1 == v;

typedef lemma void tso_read_ctxt<a>(void **pp, void *v, predicate(a) p, fixpoint(a, a, bool) le, a a0, a a1, predicate() P)(a a);
    requires le(a0, a) == true &*& p(a) &*& is_tso_read_op(?op, pp, v, ?pre, ?post) &*& pre() &*& [_]P();
    ensures p(a) &*& le(a1, a) == true &*& post() &*& is_tso_read_op(op, pp, v, pre, post);

@*/

void *tso_read/*@ <a> @*/(prophecy_id prophecyId, void **pp, int fid, ...);
    //@ requires [?f]tso<a>(?id, ?p, ?le, ?fs, ?a0) &*& tso_prophecy(prophecyId, ?v) &*& is_tso_read_ctxt(?ctxt, pp, v, p, le, a0, (nth(fid, fs))(cons(vararg_pointer(v), varargs), default_value), ?P) &*& [_]P();
    //@ ensures [f]tso<a>(id, p, le, fs, (nth(fid, fs))(cons(vararg_pointer(v), varargs), default_value)) &*& result == v;

/*@

typedef lemma void tso_cas_op(void **pp, void *old, void *new, void *v, predicate() pre, predicate() post)();
    requires pre() &*& *pp |-> ?v1;
    ensures post() &*& v1 == v &*& *pp |-> (v == old ? new : v);

typedef lemma void tso_cas_ctxt<a>(void **pp, void *old, void *new, void *v, predicate(a) p, fixpoint(a, a, bool) le, a p0, predicate() P, predicate(a) Q)(a p1);
    requires P() &*& le(p0, p1) == true &*& p(p1) &*& is_tso_cas_op(?op, pp, old, new, v, ?pre, ?post) &*& pre();
    ensures p(?q1) &*& le(p1, q1) == true &*& Q(q1) &*& is_tso_cas_op(op, pp, old, new, v, pre, post) &*& post();

@*/

void *tso_compare_and_swap/*@ <a> @*/(prophecy_id prophecyId, void **pp, void *old, void *new);
    //@ requires [?f]tso<a>(?id, ?p, ?le, ?fs, ?a0) &*& tso_prophecy(prophecyId, ?v) &*& is_tso_cas_ctxt(?ctxt, pp, old, new, v, p, le, a0, ?P, ?Q) &*& P();
    //@ ensures Q(?a1) &*& [f]tso<a>(id, p, le, fs, a1) &*& result == v;

#endif
