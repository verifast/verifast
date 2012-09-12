#ifndef CSET_H
#define CSET_H

struct cset;

/*@

//predicate representing the set minus the ownership of the values is vs
predicate cset(struct cset *s, list<int> res);
//predicate representing ownership of the presence of v in the set
predicate own(struct cset* s, int v, bool b);

predicate in(struct cset* s, int v) = own(s, v, true);
predicate out(struct cset* s, int v) = own(s, v, false);

/*
lemma void own_disjoint(struct cset* s, int v);
    requires own(s, v, ?b) &*& own(s, v, ?b2);
    ensures false;
    
//TODO: currently it is not possible to implement these:
//TODO: also, the current solution relies on dynamic behavior. It should be completely static.
// e.g. it should be possible to prove that result of tryget_own is true.

lemma bool tryget_own(struct cset* s, int v, real f);
    requires [f]cset(s);
    ensures result ? own(s, v, ?b, f) : [f]cset(s);
lemma bool tryget_own(struct cset* s, int v, real f);
    requires [f]cset(s);
    ensures result ? own(s, v, ?b, f) : [f]cset(s);
lemma void release_own(struct cset* s, int v, real f);
    requires own(s, v, ?b, f);
    ensures [f]cset(s);
*/
@*/

struct cset* ccreate();
    //@ requires true;
    //@ ensures cset(result, nil);

void cdispose(struct cset* s);
    //@ requires cset(s, nil);
    //@ ensures true;

void cadd(struct cset* s, int v);
    //@ requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ ensures own(s, v, true);

void cremove(struct cset* s, int v); 
    //@requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures own(s, v, false);

bool ccontains(struct cset* s, int v) ;
    //@ requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ ensures own(s, v, b) &*& result == b;


#endif
