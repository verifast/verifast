#include "stdlib.h"
#include "sset.h"

// a sequential set implementation 

struct llnode {
    int value;
    struct llnode *next;
};

// TODO: when it is possible to somehow define sset as a substitute name for llnode, use that instead
struct sset {
    struct llnode* set;
};

/*@
predicate llnode(struct llnode *node, struct llnode *next, int value) = 
    node != 0 &*&
    malloc_block_llnode(node) &*&
    node->next |-> next &*& 
    node->value |-> value;
    
predicate llseg(struct llnode *from, struct llnode *to, list<int> vs) =
    from == to ? vs == nil : llnode(from, ?next, ?value) &*& llseg(next, to, ?vst) &*& vs == cons(value, vst); 

predicate set(struct llnode *l, list<int> vs) =
    llseg(l, 0, cons(INT_MIN, snoc(vs, INT_MAX))) &*& 
    sorted(cons(INT_MIN, snoc(vs, INT_MAX))) == true;
    
predicate sset(struct sset* s, list<int> vs) =
    malloc_block_sset(s) &*&
    s->set |-> ?set &*&
    set(set, vs);
@*/


/*@
lemma void llnodes_distinct(struct llnode* n1, struct llnode *n2)
    requires llnode(n1, ?n1n, ?n1v) &*& llnode(n2, ?n2n, ?n2v);
    ensures llnode(n1, n1n, n1v) &*& llnode(n2, n2n, n2v) &*& n1 != n2;
{
    open llnode(n1, n1n, n1v); open llnode(n2, n2n, n2v);
    close llnode(n1, n1n, n1v); close llnode(n2, n2n, n2v);
}

lemma void llseg_appendnode(struct llnode* n1, struct llnode *n2, struct llnode *n3)
    requires llseg(n1, n2, ?vs) &*& llnode(n2, n3, ?n2v) &*& llnode(n3, ?n3n, ?n3v);
    ensures llseg(n1, n3, snoc(vs, n2v)) &*& llnode(n3, n3n, n3v);
{
    open llseg(n1, n2, vs);
    if(n1 != n2) {
        assert llnode(n1, ?n1n, head(vs)) &*& llseg(n1n, n2, tail(vs));
        llseg_appendnode(n1n, n2, n3);
        llnodes_distinct(n1, n3);
        close llseg(n1, n3, snoc(vs, n2v));
    } else {
        close llseg(n3, n3, nil);
        llnodes_distinct(n2, n3);
        close llseg(n2, n3, cons(n2v, nil));
    }
}

lemma void llseg_llnode_distinct(struct llnode* n1, struct llnode *n2, struct llnode* n3, struct llnode *n4)
    requires llseg(n1, n2, ?vs1) &*& llnode(n3, n4, ?vs2) &*& n1 != n2;
    ensures llseg(n1, n2, vs1) &*& llnode(n3, n4, vs2) &*& n1 != n3;
{
    open llseg(n1, n2, vs1);
    llnodes_distinct(n1, n3);
    close llseg(n1, n2, vs1);
}
lemma void llsegs_distinct(struct llnode* n1, struct llnode *n2, struct llnode* n3, struct llnode *n4)
    requires llseg(n1, n2, ?vs1) &*& llseg(n3, n4, ?vs2) &*& n1 != n2 &*& n3 != n4;
    ensures llseg(n1, n2, vs1) &*& llseg(n3, n4, vs2) &*& n1 != n3;
{
    open llseg(n3, n4, vs2);
    assert llnode(n3, ?n3n, ?n3v);
    llseg_llnode_distinct(n1, n2, n3, n3n);
    close llseg(n3, n4, vs2);
}

lemma void llseg_append(struct llnode* n1, struct llnode *n2, struct llnode *n3)
    requires llseg(n1, n2, ?vs1) &*& llseg(n2, n3, ?vs2) &*& llseg(n3, 0, ?vs3);
    ensures llseg(n1, n3, append(vs1, vs2)) &*& llseg(n3, 0, vs3);
{
    open llseg(n1, n2, vs1);
    if(n1 != n2) {
        assert llnode(n1, ?n1n, head(vs1));
        llseg_append(n1n, n2, n3);
        if(n3 != 0) {
            llseg_llnode_distinct(n3, 0, n1, n1n);
        } else {
            open llnode(n1, n1n, head(vs1));
            close llnode(n1, n1n, head(vs1));
        }
        close llseg(n1, n3, append(vs1, vs2));
    }
}
lemma void llseg_append_end(struct llnode* n1, struct llnode *n2)
    requires llseg(n1, n2, ?vs1) &*& llseg(n2, 0, ?vs2);
    ensures llseg(n1, 0, append(vs1, vs2));
{
    close llseg(0, 0, nil);
    llseg_append(n1, n2, 0);
    open llseg(0, 0, nil);
}
@*/



struct sset* screate() 
    //@requires true;
    //@ensures sset(result, nil);
{
    struct llnode* t = malloc(sizeof(struct llnode));
    if(t == 0) abort();
    t->value = INT_MAX;
    t->next = 0;
    //@ close llnode(t, 0, INT_MAX);
    //@ close llseg(0, 0, nil);
    //@ close llseg(t, 0, snoc(nil, INT_MAX));
    struct llnode* h = malloc(sizeof(struct llnode));
    if(h == 0) abort();
    h->value = INT_MIN;
    h->next = t;
    //@ close llnode(h, t, INT_MIN);
    //@ close llseg(h, 0, cons(INT_MIN, snoc(nil, INT_MAX)));
    //@ close set(h, nil);
    
    struct sset* s = malloc(sizeof(struct sset));
    if(s == 0) abort();
    s->set = h;
    //@ close sset(s, nil);
    return s;
}
void sdispose(struct sset* s) 
    //@requires sset(s, ?vs);
    //@ensures true;
{
    //@ open sset(s, vs);
    struct llnode* l = s->set;
    free(s);
    
    //@ open set(l, vs);
    struct llnode *c = l; 
    
    while(c!=0) 
    //@ invariant llseg(c, 0, ?rvs);
    {
        //@ open llseg(c, 0, rvs);
        //@ open llnode(c, ?cn, ?cv);
        struct llnode* n = c->next;
        free(c);
        c = n;
    }
    //@ open llseg(c, 0, rvs);
}


struct llnode* slocate(struct llnode* s, int v) 
//@ requires set(s, ?vs) &*& v > INT_MIN &*& v < INT_MAX;
/*@ ensures llseg(s, result, ?vs1) &*& llnode(result, ?rn, ?rv) &*& llnode(rn, ?rnn, ?rnv) &*& llseg(rnn, 0, ?vs2) &*& 
        cons(INT_MIN, snoc(vs, INT_MAX)) == append(vs1, cons(rv, cons(rnv, vs2))) &*& rv < v &*& v <= rnv &*& 
        sorted(cons(INT_MIN, snoc(vs, INT_MAX))) == true;
@*/
{
    //@ open set(s, vs);
    struct llnode* p = s;
    //@ open llseg(p, 0, cons(INT_MIN, snoc(vs, INT_MAX)));
    //@ open llnode(p, ?sn, INT_MIN); 
    struct llnode* c = p->next;
    //@ close llnode(p, sn, INT_MIN); 
    //@ open llseg(c, 0, snoc(vs, INT_MAX));
    //@ assert c!=0;
    //@ open llnode(c, ?cnext, ?cvalue);
    int cv = c->value;
    //@ close llnode(c, cnext, cvalue);
    //@ close llseg(s, s, nil);
    
    while(cv < v) 
/*@ invariant llseg(s, p, ?vs1) &*& llnode(p, c, ?pv) &*& llnode(c, ?cn, cv) &*& llseg(cn, 0, ?vs2) &*& 
        cons(INT_MIN, snoc(vs, INT_MAX)) == append(vs1, cons(pv, cons(cv, vs2))) &*& pv < v;
@*/
    {
        //@ struct llnode* oldp = p;
        //@ struct llnode* oldc = c;
        //@ int oldcv = cv;
        
        p = c;
        //@ open llnode(c, cn, cv);        
        c = c->next;
        //@ close llnode(p, cn, cv);
        //@ open llseg(c, 0, vs2);
        //c==0 implies cv == INT_MAX, which conflicts with cv < v
        //prove this using cons(INT_MIN, snoc(vs, INT_MAX)) == append(vs1, cons(pv, cons(cv, vs2)))
        //@ if(c == 0) { last_eq(vs, vs1, pv, cv); }
        //@ open llnode (c, ?cn2, ?cv2);
        cv = c->value;
        //@ close llnode (c, cn2, cv2);
        //@ llseg_appendnode(s, oldp, p);
        //@ append_snoc(vs1, pv, cons(oldcv, vs2));
    }
    return p;
}


bool scontains(struct sset* s, int v) 
    //@requires sset(s, ?vs) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures sset(s, vs) &*& result == mem(v, vs); 
{
    //@ open sset(s, vs);
    struct llnode* l = s->set;
    
    struct llnode* p = slocate(l, v);
    //@ open llnode(p, ?pn, ?pv);
    struct llnode* c = p->next;
    //@ open llnode(c, ?cn, ?cv);
    bool result = (c->value == v);
    //@ close llnode(c, cn, cv);    
    //@ close llnode(p, pn, pv);
    //@ assert llseg(l, p, ?vs1) &*& llseg(cn, 0, ?vs2);
    //@ close llseg (c, 0, cons(cv, vs2));
    //@ close llseg (p, 0, cons(pv, cons(cv, vs2)));
    //@ llseg_append_end(l, p);
    //@ close set(l, vs);
    //@ close sset(s, vs);
    //@ mem_snoc(v, vs, INT_MAX);
    //@ sorted_mem_append(v, vs1, pv, cons(cv, vs2)); // mem(v, append(vs1, cons(pv, cons(cv, vs2)))) == mem(v, cons(cv, vs2))
    //@ sorted_append_split(vs1, cons(pv, cons(cv, vs2)));
    //@ if(!result) sorted_mem_cons(v, cv, vs2);
    return result;
}


void sadd(struct sset* s, int v) 
    //@requires sset(s, ?vs) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures sset(s, sorted_insert(v, vs));
{
    //@ open sset(s, vs);
    struct llnode* l = s->set;
    
    struct llnode* p = slocate(l, v);
    //@ assert llseg(l, p, ?vs1);
    //@ open llnode(p, ?pn, ?pv);
    struct llnode* c = p->next;
    //@ open llnode(c, ?cn, ?cv);
    //@ assert llseg(cn, 0, ?vs2);
    //@ si1(v, vs);
    if(c->value != v) {
        struct llnode* n = malloc(sizeof(struct llnode));
        if(n == 0) abort();
        n->value = v;
        n->next = c;
        p->next = n;
        //@ close llnode(n, c, v);
        //@ close llnode(c, cn, cv);
        //@ close llseg(c, 0, cons(cv, vs2));
        //@ close llnode(p, n, pv);
        //@ close llseg(n, 0, cons(v, cons(cv, vs2)));
        //@ close llseg(p, 0, cons(pv, cons(v, cons(cv, vs2))));
        //@ llseg_append_end(l, p);
        //@ si2(v, vs1, pv, cv, vs2);
        //@ sorted_insert_sorted(v, cons(INT_MIN,snoc(vs, INT_MAX)));
    } else {
        //@ close llnode(c, cn, cv);
        //@ close llseg(c, 0, cons(cv, vs2));
        //@ close llnode(p, pn, pv);
        //@ close llseg(p, 0, cons(pv, cons(cv, vs2)));
        //@ llseg_append_end(l, p);
        //@ si3(v, vs1, pv, cv, vs2); 
    }
    //@ close set(l, sorted_insert(v, vs));
    //@ close sset(s, sorted_insert(v, vs));
}

void sremove(struct sset* s, int v) 
    //@requires sset(s, ?vs) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures sset(s, remove_all2(v, vs));
{
    //@ open sset(s, vs);
    struct llnode* l = s->set;
    struct llnode* p = slocate(l, v);
    //@ assert llseg(l, p, ?vs1);
    //@ open llnode(p, ?pn, ?pv);
    struct llnode* c = p->next;
    //@ open llnode(c, ?cn, ?cv);
    //@ assert llseg(cn, 0, ?vs2);
    //@ remove_helper1(v, vs);
    if(c->value == v) {
        struct llnode* n = c->next;
        p->next = n;
        free(c);
        //@ close llnode(p, n, pv);
        //@ close llseg(p, 0, cons(pv, vs2));
        //@ llseg_append_end(l, p);
        //@ remove_helper3(v, vs1, pv, cv, vs2);
        //@ remove_sorted(v,cons(INT_MIN, snoc(vs, INT_MAX)));
    } else {
        //@ close llnode(c, cn, cv);
        //@ close llseg(c, 0, cons(cv, vs2));
        //@ close llnode(p, c, pv);
        //@ close llseg(p, 0, cons(pv, cons(cv, vs2)));
        //@ llseg_append_end(l, p);
        //@ remove_helper2(v, vs1, pv, cv, vs2);
    }
    //@ sorted_cons(INT_MIN, snoc(vs, INT_MAX));
    //@ assert sorted(snoc(vs, INT_MAX))==true;
    //@ sorted_append_split2(vs, cons(INT_MAX, nil));
    //@ assert sorted(vs)==true;
    //@ sorted_remove_all2(v, vs);
    //@ close set(l, remove_all2(v, vs));
    //@ close sset(s, remove_all2(v, vs));
    
}
