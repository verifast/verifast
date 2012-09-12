#include "stdlib.h"
#include "linkedlist.h"
//@ #include "listex2.gh"

struct llnode {
    void* value;
    struct llnode *next;
};

struct linkedlist {
    struct llnode* head;
    int count;
};

/*@
predicate llnode(struct llnode *node; struct llnode *next, void* value) = 
    node != 0 &*&
    malloc_block_llnode(node) &*&
    node->next |-> next &*& 
    node->value |-> value;
    
predicate llseg(struct llnode *from, struct llnode *to; list<void*> elems) =
    from == to ? elems == nil : llnode(from, ?next, ?value) &*& llseg(next, to, ?elems0) &*& elems == cons(value, elems0); 

predicate linkedlist(struct linkedlist *list; list<void*> elems) =
    malloc_block_linkedlist(list) &*&
    list->head |-> ?head &*&
    llseg(head, 0, elems) &*&
    list->count |-> length(elems);
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

lemma void llnode_llseg_distinct(struct llnode* n1, struct llnode *n2)
    requires llnode(n1, n2, ?v) &*& llseg(n2, 0, ?vs2);
    ensures llnode(n1, n2, v) &*& llseg(n2, 0, vs2) &*& n1 != n2;
{
    if(n2 == 0) {
        open llnode(n1, n2, v);
        close llnode(n1, n2, v);
    } else {
        open llseg(n2, 0, vs2); 
        llnodes_distinct(n1, n2);
        close llseg(n2, 0, vs2); 
    }
}

lemma void llseg_traverse_helper(struct llnode* n1, struct llnode *n2, struct llnode *n3)
    requires llseg(n1, n2, ?vs1) &*& llnode(n2, n3, ?v) &*& llseg(n3, 0, ?vs2);
    ensures llseg(n1, n3, snoc(vs1, v)) &*& llseg(n3, 0, vs2);
{
    llnode_llseg_distinct(n2, n3);
    assert n2 != n3;
    close llseg(n3, n3, nil);
    close llseg(n2, n3, cons(v,nil));
    llseg_append(n1, n2, n3);
}


lemma void llseg_traverse2_helper(struct llnode* n1, struct llnode *n2, struct llnode *n3, struct llnode *n4)
    requires llseg(n1, n2, ?vs1) &*& llnode(n2, n3, ?v) &*& llnode(n3, n4, ?v2) &*& llseg(n4, 0, ?vs2);
    ensures llseg(n1, n3, snoc(vs1, v)) &*& llnode(n3, n4, v2) &*& llseg(n4, 0, vs2);
{
    llseg_appendnode(n1, n2, n3);
}
@*/

struct linkedlist* linkedlist_create()
    //@requires true;
    //@ensures linkedlist(result, nil);
{
    struct linkedlist* list = malloc(sizeof(struct linkedlist));
    if(list == 0) abort();
    list->head = 0;
    list->count = 0;
    return list;
}

void linkedlist_dispose(struct linkedlist* list)
    //@requires linkedlist(list, ?elems);
    //@ensures true;
{
    struct llnode* l = list->head;
    free(list);
    
    struct llnode *c = l; 
    while(c!=0) 
    //@ invariant llseg(c, 0, ?relems);
    {
        struct llnode* n = c->next;
        free(c);
        c = n;
    }
}

void linkedlist_add(struct linkedlist* list, void* elem)
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, cons(elem, elems));
{
    // @ open linkedlist(list, elems);
    if(list->count == INT_MAX) abort();
    struct llnode* head = list->head;
    struct llnode* node = malloc(sizeof(struct llnode));
    if(node == 0) abort();
    node->value = elem;
    node->next = head;
    list->head = node;
    list->count++;
}

bool linkedlist_contains(struct linkedlist* list, void* elem)
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, elems) &*& result == mem(elem, elems);
{
    //@struct llnode *h = list->head;
    struct llnode *c = list->head; 
    //@ close llseg(c, c, nil);
    while(c!=0 && c->value != elem) 
    //@ invariant list->head |-> h &*& llseg(h, c, ?lelems) &*& !mem(elem, lelems) &*& llseg(c, 0, ?relems) &*& elems == append(lelems, relems);
    {
        //@ open llseg(c, 0, relems);
        //@ open llnode(c, _, _);
        struct llnode* n = c->next;
        //@ void* v = c->value;
        //@ close llnode(c, n, v);
        //@ assert llseg(n, 0, ?relems0);
        //@ llseg_traverse_helper(h,c,n);
        c = n;
        //@ mem_snoc(elem, lelems, v);
        //@ append_cons_r_snoc_l(lelems, v, relems0);
    }
    //@ mem_append(elem, lelems, relems);
    /*@ if(c!=0) llseg_append_end(h, c);
        else open llseg(c, 0, _); 
    @*/
    return c != 0;
}

void linkedlist_remove(struct linkedlist* list, void* elem)
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, remove(elem, elems));
{
    //@ open linkedlist(list, elems);
    //@ struct llnode *h = list->head;
    struct llnode *p = list->head;
    //@ open llseg(p, 0, elems);
    if(p==0) {
        //@ close llseg(p, 0, elems);
        return;
    } 
    struct llnode *c = p->next;
    // @ assert llseg(c, 0, ?elems0); 
    if(p->value == elem) {
        list->head = c;
        list->count--;
        free(p);
        return;
    }
    //@ close llseg(p, p, nil);
    while(c!=0 && c->value != elem) 
    //@ invariant list->head |-> h &*& llseg(h, p, ?lelems) &*& !mem(elem, lelems) &*& llnode(p, c, ?v) &*& v != elem &*& llseg(c, 0, ?relems) &*& elems == append(lelems, cons(v, relems));
    {
        //@ open llseg(c, 0, relems);
        //@ open llnode(c, _, _);
        struct llnode* n = c->next;
        //@ void* v2 = c->value;
        //@ close llnode(c, n, v2);
        //@ assert llseg(n, 0, ?relems0);
        //@ llseg_traverse2_helper(h,p,c,n);
        p = c;
        c = n;
        //@ mem_snoc(elem, lelems, v);
        //@ append_cons_r_snoc_l(lelems, v, cons(v2, relems0));
    }
    //@ remove_append(elem, lelems, cons(v, relems));
    if(c!=0) {
        p->next = c->next;
        list->count--;
        free(c);
        //@ close llnode(p, ?n, v);
        //@ close llseg(p, 0, _);
        //@ llseg_append_end(h, p);
        //@ assert elems == append(lelems, cons(v, relems));
    } else {
        //@ llseg_traverse_helper(h,p,c);
        //@ open llseg(c,0,_);
    }
}


bool linkedlist_is_empty(struct linkedlist* list)
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, elems) &*& result == (elems == nil);
{
    //@ open linkedlist(list, elems);
    struct llnode* h = list->head;
    //@ open llseg(h, 0, elems);
    //@ close llseg(h, 0, elems);
    //@ close linkedlist(list, elems);
    return h == 0;
}
void* linkedlist_pop(struct linkedlist* list)
    //@requires linkedlist(list, ?elems) &*& elems != nil;
    //@ensures linkedlist(list, tail(elems)) &*& result == head(elems);
{
    //@ open linkedlist(list, elems);
    struct llnode *p = list->head;
    //@ open llseg(p, 0, elems);
    struct llnode *c = p->next;
    void* result =  p->value;
    list->head = c;
    list->count--;
    free(p);
    //@ close linkedlist(list, _);
    return result;
}

int linkedlist_count(struct linkedlist* list)
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, elems) &*& result == length(elems);
{
    return list->count;
}


void linkedlist_add_end(struct linkedlist* list, void* elem)
    //@requires linkedlist(list, ?elems);
    //@ensures linkedlist(list, snoc(elems, elem));
{

    //@ open linkedlist(list, elems);
    if(list->count == INT_MAX) abort();
    struct llnode* node = malloc(sizeof(struct llnode));
    if(node == 0) abort();
    node->value = elem;
    node->next = 0;
    //@ close llnode(node, 0, elem);
    list->count++;
    //@ struct llnode *h = list->head;
    struct llnode *p = list->head;
    //@ open llseg(p, 0, elems);
    if(p==0) {
        list->head = node;
        //@ close llseg(node, 0, cons(elem, nil));
        return;
    } 
    struct llnode *c = p->next;
    //@ close llseg(p, p, nil);
    while(c!=0) 
    //@ invariant list->head |-> h &*& llseg(h, p, ?lelems) &*& llnode(p, c, ?v) &*& llseg(c, 0, ?relems) &*& elems == append(lelems, cons(v, relems));
    {
        //@ llseg_traverse_helper(h, p, c);
        //@ open llseg(c, 0, relems);
        p = c;
        //@ open llnode(c, _, _);
        c = c->next;
        //@ close llnode(p, c, _);
        //@ append_cons_r_snoc_l(lelems, v, relems);
    }
    //@ open llseg(c, 0, _);
    //@ open llnode(p, c, v);
    p->next = node;
    //@ close llnode(p, node, v);
    //@ llnodes_distinct(p, node);
    //@ assert llnode(node, 0, elem);
    //@ close llseg(p, 0, cons(v, cons(elem, nil)));
    //@ llseg_append_end(h, p);
    //@ append_cons_r_snoc_l(lelems, v, cons(elem, nil));
}

