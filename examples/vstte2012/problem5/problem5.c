#include "stdlib.h"
//@ #include "lset.gh"
//@ #include "nat.gh"

struct vertex;

typedef struct vertex *vertex;

struct vertex_set {
    struct vertex *value;
    struct vertex_set *next;
};

/*@
predicate vsnode(struct vertex_set* node; struct vertex_set* next, struct vertex* value) = 
    malloc_block_vertex_set(node) &*& node != 0 &*& 
    node->value |-> value &*&
    node->next |-> next;

lemma void vsnode_distinct(struct vertex_set *n1, struct vertex_set *n2)
    requires vsnode(n1, ?n1n, ?n1v) &*& vsnode(n2, ?n2n, ?n2v);
    ensures vsnode(n1, n1n, n1v) &*& vsnode(n2, n2n, n2v) &*& n1 != n2;
{
    open vsnode(n1, n1n, n1v);
    open vsnode(n2, n2n, n2v);
}

predicate vsseg(struct vertex_set* from, struct vertex_set* to; list<struct vertex*> values) = 
    from == to ? values == nil : vsnode(from, ?next, ?value) &*& vsseg(next, to, ?values2) &*& values == cons(value, values2);

predicate vs(struct vertex_set* node; list<struct vertex*> values) = 
    vsseg(node, 0, values);

lemma void vsseg_append(struct vertex_set* from, struct vertex_set* to)
    requires vsseg(from, to, ?vs) &*& vsnode(to, ?next, ?v) &*& vs(next, ?vs2);
    ensures vsseg(from, next, snoc(vs, v)) &*& vs(next, vs2);
{
    open vsseg(from, to, vs);
    if (from == to) {
        open vs(next, vs2);
        open vsseg(next, 0, vs2);
        if (next == 0) {
            open vsnode(to, next, v);
            close vsnode(to, next, v);
        } else
            vsnode_distinct(to, next);
        close vsseg(next, 0, vs2);
        close vs(next, vs2);
        close vsseg(from, next, snoc(vs, v));
    } else {
        assert vsseg(?from2, to, ?vst);
        open vs(next, vs2);
        open vsseg(next, 0, vs2);
        if (next == 0) {
            open vsnode(from, from2, ?vf);
            close vsnode(from, from2, vf);
        } else
            vsnode_distinct(from, next);
        close vsseg(next, 0, vs2);
        close vs(next, vs2);
        vsseg_append(from2, to);
        close vsseg(from, next, snoc(vs, v));
    }
}

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

/*@

lemma void distinct_map_eq<a, b>(list<a> xs, a x, a y, fixpoint(a, b) f)
    requires mem(x, xs) && mem(y, xs) && distinct(map(f, xs)) && f(x) == f(y);
    ensures x == y;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                if (x0 != y) {
                     mem_map(y, xs0, f);
                     assert false;
                }
            } else if (x0 == y) {
                mem_map(x, xs0, f);
                assert false;
            } else {
                distinct_map_eq(xs0, x, y, f);
            }
     }
}

@*/

struct vertex_set *vs_remove(struct vertex_set* vs, struct vertex* v) 
   //@ requires vs(vs, ?l) &*& exists<list<struct vertex *> >(?allvs) &*& lset_subset(l, allvs) && mem(v, allvs) && distinct(map(address_of, allvs));
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
            //@ assert address_of(vs->value) == address_of(v);
            //@ assert mem(vs->value, allvs) == true;
            //@ distinct_map_eq(allvs, vs->value, v, address_of);
            //@ assert vs->value == v;
            free(vs);
            return newnext;
        } else {
            vs->next = newnext;
            //@ close vsnode(vs, newnext, vsv);
            //@ close vs(vs, lset_remove(l, v));
            return vs;
        }
    }
}

bool vs_contains(struct vertex_set* vs, struct vertex* v) 
    //@ requires vs(vs, ?l) &*& exists<list<struct vertex *> >(?allvs) &*& lset_subset(l, allvs) && distinct(map(address_of, allvs)) && mem(v, allvs);
    //@ ensures vs(vs, l) &*& result == lset_contains(l, v);
{
    //@ open vsseg(vs, 0, l);
    if(vs == 0) { 
        //@ close vs(vs, l);
        return false;
    } else {
        //@ open vsnode(vs, ?next, ?value);
        if(vs->value == v) {
            //@ distinct_map_eq(allvs, vs->value, v, address_of);
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

lemma void foreach2_length<a, b>(list<a> xs)
    requires foreach2<a, b>(xs, ?ys, ?p);
    ensures foreach2<a, b>(xs, ys, p) &*& length(ys) == length(xs);
{
    open foreach2(xs, ys, p);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            foreach2_length(xs0);
    }
    close foreach2(xs, ys, p);
}

lemma void foreach2_remove<a, b>(a x, list<a> xs)
    requires foreach2<a, b>(xs, ?ys, ?p) &*& mem(x, xs) == true;
    ensures foreach2<a, b>(remove(x, xs), remove2(x, xs, ys), p) &*& p(x, assoc2(x, xs, ys)) &*& length(ys) == length(xs);
{
    open foreach2(xs, ys, p);
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                foreach2_length(xs0);
            } else {
                foreach2_remove(x, xs0);
                close foreach2(remove(x, xs), remove2(x, xs, ys), p);
            }
    }
}

lemma void foreach2_unremove<a, b>(a x, list<a> xs, list<b> ys)
    requires foreach2<a, b>(remove(x, xs), remove2(x, xs, ys), ?p) &*& mem(x, xs) == true &*& length(ys) == length(xs) &*& p(x, assoc2(x, xs, ys));
    ensures foreach2<a, b>(xs, ys, p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                close foreach2(xs, ys, p);
            } else {
                switch (ys) { case nil: case cons(y0, ys0): }
                open foreach2(remove(x, xs), remove2(x, xs, ys), p);
                foreach2_unremove(x, xs0, tail(ys));
                close foreach2(xs, ys, p);
            }
    }
}

lemma void foreach2_update<a, b>(a x, b y, list<a> xs, list<b> ys)
    requires foreach2<a, b>(remove(x, xs), remove2(x, xs, ys), ?p) &*& mem(x, xs) == true &*& length(ys) == length(xs) &*& p(x, y);
    ensures foreach2<a, b>(xs, update2(x, y, xs, ys), p);
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                close foreach2(xs, update2(x, y, xs, ys), p);
            } else {
                switch (ys) { case nil: case cons(y0, ys0): }
                open foreach2(remove(x, xs), remove2(x, xs, ys), p);
                foreach2_update(x, y, xs0, tail(ys));
                close foreach2(xs, update2(x, y, xs, ys), p);
            }
    }
}

fixpoint uintptr_t address_of(void *p) { return (uintptr_t)p; }

predicate graph(list<struct vertex *> allvs, list<list<struct vertex *> > succs) =
    distinct(map(address_of, allvs)) == true &*&
    foreach2(allvs, succs, gvertex(allvs));

lemma void lset_subset_add_r<t>(list<t> s1, list<t> s2, t el)
    requires lset_subset(s1, s2) == true;
    ensures lset_subset(s1, lset_add(s2, el)) == true;
{
    switch(s1) {
        case nil:
        case cons(h,t):
            lset_subset_add_r(t, s2, el);
    }
}

lemma void graph_add_vertex(vertex v, list<vertex> allvs)
    requires foreach2(?vs, ?edges, gvertex(allvs)) &*& v->succ |-> ?succ;
    ensures foreach2(vs, edges, gvertex(cons(v, allvs))) &*& v->succ |-> succ &*& !mem(address_of(v), map(address_of, vs));
{
    open foreach2(vs, edges, _);
    switch (vs) {
        case nil:
        case cons(v0, vs0):
            open gvertex(allvs)(v0, head(edges));
            open vertex(v0, head(edges), allvs);
            lset_subset_add_r(head(edges), allvs, v);
            close vertex(v0, head(edges), cons(v, allvs));
            close gvertex(cons(v, allvs))(v0, head(edges));
            graph_add_vertex(v, allvs);
    }
    close foreach2(vs, edges, gvertex(cons(v, allvs)));
}

lemma void create_graph()
    requires true;
    ensures graph(nil, nil);
{
    close foreach2(nil, nil, gvertex(nil));
    close graph(nil, nil);
}

@*/

vertex add_vertex()
    //@ requires graph(?allvs, ?allsuccs);
    //@ ensures graph(cons(result, allvs), cons(nil, allsuccs)) &*& distinct(map(address_of, cons(result, allvs))) == true;
{
    vertex v = malloc(sizeof(struct vertex));
    if (v == 0) abort();
    v->succ = 0;
    return v;
    //@ open graph(allvs, allsuccs);
    //@ graph_add_vertex(v, allvs);
    //@ close vertex(v, nil, cons(v, allvs));
    //@ close gvertex(cons(v, allvs))(v, nil);
    //@ close foreach2(cons(v, allvs), cons(nil, allsuccs), gvertex(cons(v, allvs)));
    //@ close graph(cons(v, allvs), cons(nil, allsuccs));
}

/*@

fixpoint list<b> update2<a, b>(a x, b y, list<a> xs, list<b> ys) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0): return x0 == x ? cons(y, tail(ys)) : cons(head(ys), update2(x, y, xs0, tail(ys)));
    }
}
            
@*/

void add_edge(vertex v1, vertex v2)
    //@ requires graph(?allvs, ?allsuccs) &*& mem(v1, allvs) == true &*& mem(v2, allvs) == true;
    //@ ensures graph(allvs, update2(v1, cons(v2, assoc2(v1, allvs, allsuccs)), allvs, allsuccs));
{
    //@ open graph(allvs, allsuccs);
    //@ foreach2_remove(v1, allvs);
    //@ open gvertex(allvs)(v1, ?succs);
    //@ open vertex(v1, succs, allvs);
    struct vertex_set *succ = vs_add(v1->succ, v2);
    v1->succ = succ;
    //@ close vertex(v1, cons(v2, succs), allvs);
    //@ close gvertex(allvs)(v1, cons(v2, succs));
    //@ foreach2_update(v1, cons(v2, succs), allvs, allsuccs);
    //@ close graph(allvs, update2(v1, cons(v2, assoc2(v1, allvs, allsuccs)), allvs, allsuccs));
}

/*@

fixpoint list<struct vertex *> get_succs(list<struct vertex *> vs, list<list<struct vertex *> > edges, struct vertex *v) {
    return assoc2(v, vs, edges);
}

fixpoint list<a> concat<a>(list<list<a> > xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0): return append(x0, concat(xs0));
    }
}

fixpoint list<struct vertex *> reachn(nat n, struct vertex *source, list<struct vertex *> vs, list<list<struct vertex *> > edges) {
    switch (n) {
        case zero: return cons(source, nil);
        case succ(n0): return append(concat(map((get_succs)(vs, edges), reachn(n0, source, vs, edges))), reachn(n0, source, vs, edges));
    }
}

typedef lemma void not_reachable(struct vertex *source, list<struct vertex *> vs, list<list<struct vertex *> > edges, struct vertex *v)(nat n);
    requires mem(v, reachn(n, source, vs, edges)) == true;
    ensures false;

fixpoint bool has_mindist(vertex source, list<vertex> vs, list<list<vertex> > edges, nat n, vertex v) {
    return mem(v, reachn(n, source, vs, edges)) &&
      switch (n) { case zero: return true; case succ(n0): return !mem(v, reachn(n0, source, vs, edges)); };
}

lemma void forall_lset_remove<t>(list<t> xs, fixpoint(t, bool) p, t x)
    requires forall(xs, p) == true;
    ensures forall(lset_remove(xs, x), p) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            forall_lset_remove(xs0, p, x);
    }
}

lemma void mem_concat_map<a, b>(fixpoint(a, list<b>) f, list<a> xs, a x, b y)
    requires mem(x, xs) == true &*& mem(y, f(x)) == true;
    ensures mem(y, concat(map(f, xs))) == true;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (x0 == x) {
                assert concat(map(f, xs)) == append(f(x0), concat(map(f, xs0)));
            } else {
                mem_concat_map(f, xs0, x, y);
            }
            lset_union_contains(f(x0), concat(map(f, xs0)), y);
    }
}

lemma void reachn_succ(nat n, vertex source, list<vertex> vs, list<list<vertex> > edges, vertex v, vertex w)
    requires mem(v, reachn(n, source, vs, edges)) == true &*& mem(w, assoc2(v, vs, edges)) == true;
    ensures mem(w, reachn(succ(n), source, vs, edges)) == true;
{
    assert mem(w, get_succs(vs, edges, v)) == true;
    mem_concat_map((get_succs)(vs, edges), reachn(n, source, vs, edges), v, w);
    lset_union_contains(concat(map((get_succs)(vs, edges), reachn(n, source, vs, edges))), reachn(n, source, vs, edges), w);
}

@*/


int bfs(struct vertex* source, struct vertex* dest) 
   //@ requires graph(?allvs, ?allsuccs) &*& lset_contains(allvs, source) == true &*& lset_contains(allvs, dest) == true;
   /*@
   ensures
       graph(allvs, allsuccs) &*&
//       result < 0 ?
//           is_not_reachable(?lem, source, allvs, allsuccs, dest)
//       :
//           has_mindist(source, allvs, allsuccs, nat_of_int(result), dest) == true;
       result < 0 || mem(dest, reachn(nat_of_int(result), source, allvs, allsuccs));
   @*/
{
    struct vertex_set* visited = vs_singleton(source);
    struct vertex_set* current = vs_singleton(source);
    struct vertex_set* new = vs_empty();
    int distance = 0;
    while(!vs_isempty(current)) 
    /*@ invariant graph(allvs, allsuccs) &*& vs(visited, ?visitedv) &*& vs(current, ?currentv) &*& vs(new, ?newv) &*&
            0 <= distance &*&
            lset_subset(visitedv, allvs) == true &*& lset_subset(currentv, visitedv) == true &*& lset_subset(newv, visitedv) == true &*&
            forall(currentv, (lset_contains)(reachn(nat_of_int(distance), source, allvs, allsuccs))) == true &*&
            forall(newv, (lset_contains)(reachn(succ(nat_of_int(distance)), source, allvs, allsuccs))) == true;
    @*/
    {
        //@ open vsseg(current, 0, currentv);
        //@ assert current != 0;
        //@ open vsnode(current, _, _);
        struct vertex *v = current->value;
        //@ close vsnode(current, _, v);
        //@ close vs(current, currentv);  
        //@ close exists(allvs);
        //@ lset_subset_trans(currentv, visitedv, allvs);
        //@ open graph(allvs, allsuccs);
        //@ close graph(allvs, allsuccs);
        current = vs_remove(current, v);
        //@ forall_lset_remove(currentv, (lset_contains)(reachn(nat_of_int(distance), source, allvs, allsuccs)), v);
        //@ assert vs(current, ?currentvnew) &*& forall(currentvnew, (lset_contains)(reachn(nat_of_int(distance), source, allvs, allsuccs))) == true;
        
        if(v == dest) 
        {
            //@ distinct_map_eq(allvs, v, dest, address_of);
            vs_dispose(current);
            vs_dispose(visited);
            vs_dispose(new);
            return distance;
        }
        
        //@ lset_subset_contains(currentv, visitedv, v);
        //@ lset_subset_contains(visitedv, allvs, v);
        //@ assert lset_contains(allvs, v) == true;
        //@ open graph(allvs, allsuccs);
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
                assert false;
            }
        @*/
        /*@    
            if(! lset_equals(newv, lset_union(newv, lset_diff(nil, visitedv))) ) {
                lset_equals_contains_conv(newv, lset_union(newv, lset_diff(nil, visitedv)));
                assert false;
            }
        @*/
        while(succs != 0)
        /*@ invariant vsseg(h, succs, ?succsvl) &*& vs(succs, ?succsvr) &*& succsv == append(succsvl, succsvr) &*&
                vs(visited, ?visitedv2) &*& lset_equals(visitedv2, lset_union(visitedv, succsvl)) == true &*& 
                vs(new, ?newv2) &*& lset_equals(newv2, lset_union(newv, lset_diff(succsvl, visitedv))) == true &*&
                forall(newv2, (lset_contains)(reachn(succ(nat_of_int(distance)), source, allvs, allsuccs))) == true;
        @*/
        {
            //@ open vsseg(succs, 0, succsvr);
            //@ open vsnode(succs, _, _);
            struct vertex* w = succs->value;
            //@ lset_equals_contains(visitedv2, lset_union(visitedv, succsvl), w);
            //@ lset_union_contains(visitedv, succsvl, w);
            //@ lset_subset_union_l(succsvl, succsvr);
            //@ lset_subset_trans(succsvl, append(succsvl, succsvr), allvs);
            //@ assert lset_subset(visitedv, allvs) && lset_subset(succsvl, allvs);
            //@ lset_union_subset_l(visitedv, succsvl, allvs);
            //@ lset_subset_trans(visitedv2, lset_union(visitedv, succsvl), allvs);
            //@ lset_subset_contains(succsv, allvs, w);
            //@ close exists(allvs);
            if(!vs_contains(visited, w)) 
            {
                //@ assert lset_contains(visitedv2, w) == false;
                //@ assert lset_contains(visitedv, w) == false;
                visited = vs_add(visited, w);
                new = vs_add(new, w);
                //@ assert succsv == assoc2(v, allvs, allsuccs);
                //@ assert mem(w, succsvr) == true;
                //@ lset_union_contains(succsvl, succsvr, w);
                //@ assert mem(w, succsv) == true;
                //@ assert mem(v, allvs) == true &*& mem(w, assoc2(v, allvs, allsuccs)) == true;
                //@ reachn_succ(nat_of_int(distance), source, allvs, allsuccs, v, w);
                //@ assert mem(w, reachn(succ(nat_of_int(distance)), source, allvs, allsuccs)) == true;
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
                if (lset_contains(succsvl, x))
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
                    if (lset_contains(newv, x))
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
                    if (lset_contains(newv, x))
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

/*@

lemma void note(bool b)
    requires b;
    ensures b;
{
}

@*/

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    //@ create_graph();
    vertex v1 = add_vertex();
    vertex v2 = add_vertex();
    vertex v3 = add_vertex();
    vertex v4 = add_vertex();
    add_edge(v1, v2);
    add_edge(v2, v3);
    add_edge(v3, v4);
    add_edge(v2, v4);
    int d = bfs(v1, v4);
    //@ note(nat_of_int(3) == succ(succ(succ(zero))));
    assert(d != 0);
    assert(d != 1);
    // TODO: Prove d == 2
    
    vertex v5 = add_vertex();
    d = bfs(v1, v5);
    assert(d != 0);
    assert(d != 1);
    assert(d != 2);
    assert(d != 3);
    // TODO: Prove d < 0
    
    return 0;
    //@ leak graph(_, _);
}