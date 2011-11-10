#include "stdlib.h"
//@ #include "lset.h"

struct vertex;

struct vertex_set {
    struct vertex *value;
    struct vertex_set *next;
};

/*@
predicate vsnode(struct vertex_set* node; struct vertex_set* next, struct vertex* value) = 
    malloc_block_vertex_set(node) &*& node != 0 &*& 
    node->value |-> value &*&
    node->next |-> next;

predicate vsseg(struct vertex_set* from, struct vertex_set* to; list<struct vertex*> values) = 
    from == to ? values == nil : vsnode(from, ?next, ?value) &*& vsseg(next, to, ?values2) &*& values == cons(value, values2);

predicate vs(struct vertex_set* node; list<struct vertex*> values) = 
    vsseg(node, 0, values);

//TODO:
lemma void vsseg_append(struct vertex_set* from, struct vertex_set* to);
    requires vsseg(from, to, ?vs) &*& vsnode(to, ?next, ?v) &*& vs(next, ?vs2);
    ensures vsseg(from, next, snoc(vs, v)) &*& vs(next, vs2);

lemma void append_cons_r<t>(list<t> l1, t v, list<t> l2)
    requires true;
    ensures append(l1, cons(v, l2)) == append(snoc(l1, v), l2);
{
    switch(l1) {
        case nil:
        case cons(h,t): append_cons_r(t, v, l2);
    }
}

@*/

struct vertex_set *vs_empty() 
   //@ requires true;
   //@ ensures vs(result, lset_empty());
{ 
    //@ close vs(0, nil);
    return 0; 
}

bool vs_isempty(struct vertex_set* vs) 
   //@ requires vs(vs, ?l);
   //@ ensures vs(vs, l) &*& result == (l == lset_empty());
{
    //@ open vsseg(vs, 0, l);
    //@ if(vs == 0) assert l == nil;
    //@ close vs(vs, l);
    return vs == 0;
}

struct vertex_set *vs_add(struct vertex_set* vs, struct vertex* v) 
   //@ requires vs(vs, ?l);
   //@ ensures vs(result, lset_add(l, v));
{ 
    struct vertex_set *res = malloc(sizeof(struct vertex_set));
    if(res == 0) abort();
    res->value = v;
    res->next = vs;
    //@ close vsnode(res, vs, v);
    //@ close vs(res, cons(v, l));
    return res; 
}

struct vertex_set *vs_singleton(struct vertex* v) 
   //@ requires true;
   //@ ensures vs(result, lset_singleton(v));
{ 
    struct vertex_set* e = vs_empty();
    return vs_add(e, v);
}

struct vertex_set *vs_remove(struct vertex_set* vs, struct vertex* v) 
   //@ requires vs(vs, ?l);
   //@ ensures vs(result, lset_remove(l, v));
{ 
    //@ open vsseg(vs, 0, l);
    if(vs == 0) {
        //@ close vs(vs, l); 
        return 0;
    } else {
        //@ open vsnode(vs, ?vsn, ?vsv);
        struct vertex_set* next = vs->next;
        struct vertex_set* newnext = vs_remove(next, v);
        if(vs->value == v) {
            free(vs);
            return newnext;
        } else {
            if(next != newnext) {
                vs->next = newnext;
            } 
            //@ close vsnode(vs, newnext, vsv);
            //@ close vs(vs, lset_remove(l, v));
            return vs;
        }
    }
}

bool vs_contains(struct vertex_set* vs, struct vertex* v) 
    //@ requires vs(vs, ?l);
    //@ ensures vs(vs, l) &*& result == lset_contains(l, v);
{
    //@ open vsseg(vs, 0, l);
    if(vs == 0) { 
        //@ close vs(vs, l);
        return false;
    } else {
        //@ open vsnode(vs, ?next, ?value);
        if(vs->value == v) {
            //@ close vsnode(vs, next, value);
            //@ close vs(vs, l);
            return true;
        } else {
            bool result = vs_contains(vs->next, v);
            //@ close vsnode(vs, next, value);
            //@ close vs(vs, l);
            return result;
        }
    }
}

void vs_dispose(struct vertex_set* vs) 
    //@ requires vs(vs, ?l);
    //@ ensures true;
{
    while(vs != 0)
        //@ invariant vs(vs, ?l2); 
    {
        //@ open vs(vs, l2);
        //@ open vsnode(vs, _, _);
        struct vertex_set* next = vs->next;
        free(vs);
        vs = next;
    }
    //@open vs(0, _);
}

struct vertex {
    struct vertex_set* succ;
};

/*@

predicate vertex(struct vertex* v, list<struct vertex *> succs, list<struct vertex *> allvs) = 
    malloc_block_vertex(v) &*& v != 0 &*&
    v->succ |-> ?succ &*&
    vs(succ, succs) &*&
    lset_subset(succs, allvs) == true;

predicate_ctor gvertex(list<struct vertex*> allvs)(struct vertex *v, list<struct vertex *> succs) =
    vertex(v, succs, allvs);

predicate foreach2<a, b>(list<a> xs, list<b> ys, predicate(a, b) p) =
    switch (xs) {
        case nil: return ys == nil;
        case cons(x, xs0): return
            switch (ys) {
                case nil: return false;
                case cons(y, ys0): return
                    p(x, y) &*& foreach2(xs0, ys0, p);
            };
    };

fixpoint list<b> remove2<a, b>(a x, list<a> xs, list<b> ys) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0): return x0 == x ? tail(ys) : cons(head(ys), remove2(x, xs0, tail(ys)));
    }
}

fixpoint b assoc2<a, b>(a x, list<a> xs, list<b> ys) {
    switch (xs) {
        case nil: return default_value;
        case cons(x0, xs0): return x0 == x ? head(ys) : assoc2(x, xs0, tail(ys));
    }
}

lemma void foreach2_remove<a, b>(a x, list<a> xs);
    requires foreach2<a, b>(xs, ?ys, ?p) &*& mem(x, xs) == true;
    ensures foreach2<a, b>(remove(x, xs), remove2(x, xs, ys), p) &*& p(x, assoc2(x, xs, ys)) &*& length(ys) == length(xs);

lemma void foreach2_unremove<a, b>(a x, list<a> xs, list<b> ys);
    requires foreach2<a, b>(remove(x, xs), remove2(x, xs, ys), ?p) &*& length(ys) == length(xs) &*& p(x, assoc2(x, xs, ys));
    ensures foreach2<a, b>(xs, ys, p);

predicate graph(list<struct vertex *> allvs, list<list<struct vertex *> > succs) =
    foreach2(allvs, succs, gvertex(allvs));

@*/


int bfs(struct vertex* source, struct vertex* dest) 
   //@ requires graph(?allvs, ?allsuccs) &*& lset_contains(allvs, source) == true &*& lset_contains(allvs, dest) == true;
   //@ ensures graph(allvs, allsuccs);
{
    struct vertex_set* visited = vs_singleton(source);
    struct vertex_set* current = vs_singleton(source);
    struct vertex_set* new = vs_empty();
    int distance = 0;
    while(!vs_isempty(current)) 
    /*@ invariant graph(allvs, allsuccs) &*& vs(visited, ?visitedv) &*& vs(current, ?currentv) &*& vs(new, ?newv) &*& 
            lset_subset(visitedv, allvs) == true &*& lset_subset(currentv, visitedv) == true &*& lset_subset(newv, visitedv) == true;
    @*/
    {
        //@ open vsseg(current, 0, currentv);
        //@ assert current != 0;
        //@ open vsnode(current, _, _);
        struct vertex *v = current->value;
        //@ close vsnode(current, _, v);
        //@ close vs(current, currentv);        
        current = vs_remove(current, v);
        
        if(v == dest) 
        {
            vs_dispose(current);
            vs_dispose(visited);
            vs_dispose(new);
            return distance;
        }
        
        //@ open graph(allvs, allsuccs);
        //@ lset_subset_contains(currentv, visitedv, v);
        //@ lset_subset_contains(visitedv, allvs, v);
        //@ assert lset_contains(allvs, v) == true;
        //@ foreach2_remove(v, allvs);
        //@ open gvertex(allvs)(v, ?vsuccs);
        //@ open vertex(v, vsuccs, allvs);
        struct vertex_set* h = v->succ;
        struct vertex_set* succs = v->succ;
        //new new = union(old new, diff(succs, visited)); 
        //new visited = union(old visited, succs)); 
        //@ assert vs(h, ?succsv) &*& lset_subset(succsv, allvs) == true;
        //@ close vsseg(h, h, nil);
        /*@
            if(! lset_equals(visitedv, lset_union(visitedv, nil)) ) {
                lset_equals_contains_conv(visitedv, lset_union(visitedv, nil));
                open exwitness(?x);
                lset_union_contains(visitedv, nil, x);
                assert false;
            }
        @*/
        /*@    
            if(! lset_equals(newv, lset_union(newv, lset_diff(nil, visitedv))) ) {
                lset_equals_contains_conv(newv, lset_union(newv, lset_diff(nil, visitedv)));
                open exwitness(?x);
                lset_union_contains(newv, lset_diff(nil, visitedv), x);
                lset_diff_contains(nil, visitedv, x);
                assert false;
            }
        @*/
        while(succs != 0)
        /*@ invariant vsseg(h, succs, ?succsvl) &*& vs(succs, ?succsvr) &*& succsv == append(succsvl, succsvr) &*&
                vs(visited, ?visitedv2) &*& lset_equals(visitedv2, lset_union(visitedv, succsvl)) == true &*& 
                vs(new, ?newv2) &*& lset_equals(newv2, lset_union(newv, lset_diff(succsvl, visitedv))) == true;
        @*/
        {
            //@ open vsseg(succs, 0, succsvr);
            //@ open vsnode(succs, _, _);
            struct vertex* w = succs->value;
            //@ lset_equals_contains(visitedv2, lset_union(visitedv, succsvl), w);
            //@ lset_union_contains(visitedv, succsvl, w);
            if(!vs_contains(visited, w)) 
            {
                //@ assert lset_contains(visitedv2, w) == false;
                //@ assert lset_contains(visitedv, w) == false;
                visited = vs_add(visited, w);
                new = vs_add(new, w);
            } else {
                //@ assert lset_contains(visitedv2, w) == true;
            }
            //@ struct vertex_set* oldsuccs = succs;
            succs = succs->next;
            //@ close vsnode(oldsuccs, succs, w);
            //@ assert vs(succs, ?newsuccsvr);
            //@ vsseg_append(h, oldsuccs);
            //@ append_cons_r(succsvl, w, newsuccsvr);
            //@ assert vs(visited, ?visitedv3) &*& vs(new, ?newv3); 
            /*@ 
                if(! lset_equals(visitedv3, lset_union(visitedv, snoc(succsvl, w))) ) {
                    lset_equals_contains_conv(visitedv3, lset_union(visitedv, snoc(succsvl, w)));
                    open exwitness(?x);
                    lset_equals_contains(visitedv2, lset_union(visitedv, succsvl), x);
                    lset_union_contains(visitedv, succsvl, x);
                    lset_union_contains(visitedv, snoc(succsvl, w), x);
                    lset_union_contains(succsvl, lset_singleton(w), x);
                    lset_add_contains(visitedv2, w, x);
                    assert false;
                }
            @*/
            /*@ 
                if(! lset_equals(newv3, lset_union(newv, lset_diff(snoc(succsvl, w), visitedv))) ) {
                    lset_equals_contains_conv(newv3, lset_union(newv, lset_diff(snoc(succsvl, w), visitedv)));
                    open exwitness(?x);
                    lset_equals_contains(newv2, lset_union(newv, lset_diff(succsvl, visitedv)), x);
                    lset_union_contains(newv, lset_diff(succsvl, visitedv), x);
                    lset_diff_contains(succsvl, visitedv, x);
                    lset_union_contains(newv, lset_diff(snoc(succsvl, w), visitedv), x);
                    lset_diff_contains(snoc(succsvl, w), visitedv, x);
                    lset_union_contains(succsvl, lset_singleton(w), x);
                    lset_add_contains(newv2, w, x);
                    assert false;
                }
            @*/
        }
        //@ assert succs == 0;
        //@ open vs(succs, _);
        //@ open vsseg(succs, 0, _);
        //@ assert succsvr == nil;
        //@ append_nil(succsv);
        //@ assert succsv == succsvl;
        
        //@ close vertex(v, vsuccs, allvs);
        //@ close gvertex(allvs)(v, vsuccs);
        //@ foreach2_unremove(v, allvs, allsuccs);
        //@ close graph(allvs, allsuccs);
        
        if(vs_isempty(current)) {
            vs_dispose(current);
            current = new;
            new = vs_empty();
            if(distance == INT_MAX) abort();
            distance = distance + 1;
        }
        
        //@ assert vs(current, ?currentv2) &*& vs(new, ?newv3);
        /*@ if(!lset_subset(visitedv2, allvs)) {
                lset_subset_contains_conv(visitedv2, allvs);
                open exwitness(?x);
                lset_equals_contains(visitedv2, lset_union(visitedv, succsvl), x);
                lset_union_contains(visitedv, succsvl, x);
                lset_subset_contains(succsvl, allvs, x); 
                lset_subset_contains(visitedv, allvs, x); 
                assert false;
            }
        @*/
        /*@ if(!lset_subset(currentv2, visitedv2)) {
                lset_subset_contains_conv(currentv2, visitedv2);
                open exwitness(?x);
                lset_equals_contains(visitedv2, lset_union(visitedv, succsvl), x);
                lset_union_contains(visitedv, succsvl, x);
                if(currentv2 == newv2) {
                    lset_subset_contains(newv, visitedv, x);
                    lset_equals_contains(newv2, lset_union(newv, lset_diff(succsvl, visitedv)), x);
                    lset_union_contains(newv, lset_diff(succsvl, visitedv), x);
                    lset_diff_contains(succsvl, visitedv, x);
                } else {
                    lset_remove_contains(currentv, v, x);
                    lset_subset_contains(currentv, visitedv, x);
                }
                assert false;
        
            }
        @*/
        /*@ if(!lset_subset(newv3, visitedv2)) {
                lset_subset_contains_conv(newv3, visitedv2);
                open exwitness(?x);
                lset_equals_contains(visitedv2, lset_union(visitedv, succsvl), x);
                lset_union_contains(visitedv, succsvl, x);
                if(newv3 != lset_empty()) {
                    lset_subset_contains(newv, visitedv, x);
                    lset_equals_contains(newv2, lset_union(newv, lset_diff(succsvl, visitedv)), x);
                    lset_union_contains(newv, lset_diff(succsvl, visitedv), x);
                    lset_diff_contains(succsvl, visitedv, x);
                }
                assert false;
            }
        @*/
    }
    vs_dispose(current);
    vs_dispose(new);
    vs_dispose(visited);
    return -1;
}