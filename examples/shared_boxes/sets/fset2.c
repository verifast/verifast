#include "stdlib.h"
#include "threading.h"
#include "mutex3.h"
//@ #include "map.gh"
//@ #include "wfmap.gh"
//@ #include "counting.gh"
//@ #include "set.gh"
//@ #include "slist.gh"

// a fine grained set implementation 

struct llnode {
    struct mutex3 *mutex;
    int value;
    struct llnode *next;
    //@ int owner;
    //@ bool malloc_ex;
};

struct fset {
    struct llnode* set;
    struct mutex* boxMutex;
    //@ list<int> res;
    //@ box boxId;
};


/*
    Changes wrt fset.c 
    1. created ghost field for owner. Guarantees that a thread remains owner of a node until it releases the node. 
       This may make it possible to simplify the box actions.
      
    2. added a fraction of the value field in the link* predicates. 
       Right now you need mem(gnode(p, c, pvalue, v), gnodes) == true to ensure that the value of p is pvalue, even if there is a link predicate. 
       This may simplify certain specifications. 
       
    3. a) added link_internal, and defined link, linkex and linkex2 based on link_internal.
       b) added value to link, linkex, linkex2
       c) moved owner param of linkex
       
    TODO: Remove unnecessary link predicates. 
    TODO: Remove unnecessary node predicates. 
    TODO: remove parameters of unlock_lockednode
*/

/*
   note about cap:
   - the cap paper every now and they seems to read a value without permission. Maybe this is because they leave out an 
     implicit partitioning step. 
   - the cap paper seems to miss a change step   
    
   shared boxes vs cap:
   - the cap paper can use existential quantifiers in the actions, and therefore leave certain things unspecified
     with shared boxes, patterns are not supported (neither in the definition nor as arguments when performing the action).

problem:
cap uses existential quantification to hide the next node (and the node) from the change action.
with shared boxes this is impossible, and therefore I cannot express the post condition.

e.g. the following action cannot be used in practice because the threads cannot specifiy the next node.

    action change(struct llnode* node, struct llnode* next, int v);
        requires map_contains(reserved, v, actionHandle) && !map_contains_key(gaps, node);
        ensures 
            allGaps == map_put(old_allGaps, v, map_put(map_get(old_allGaps, v), node, next)) && 
            gaps == map_put(old_gaps, node, next) &&
            values == old_values && 
            reserved == old_reserved;

on the other hand, without the next parameter, it is harder to specify the post condition.

    action change(struct llnode* node, int v);
        requires map_contains(reserved, v, actionHandle) && !map_contains_key(gaps, node);
        ensures 
            allGaps == map_put(old_allGaps, v, map_put(map_get(old_allGaps, v), node, ?next)) && 
            gaps == map_put(old_gaps, node, ?next) &&
            values == old_values && 
            reserved == old_reserved;
            

More abstractly put: 
an existential quantifier is usefull whenever an action needs to update the state of the box 
using a value which can only be read after starting the action.
In such cases, the value cannot be added as parameter, since it cannot be read before the action.
The only way to deal with this using shared boxes is to create an extra box variable that
stores or gives access to the variable.


we could add a full map from node to next as parameter. 
When performing a change action, the changeperm should relate the next map with the link predicate.

struct fset *s, 
list<int> values, 
map<int, handle> reserved,
map<struct llnode *, struct llnode *> nextNodes,
map<int, list<struct llnode *> > resLocked,
list<struct llnode *> allLocked

list<pair<bool, struct llnode*> >




Other note:

to fully understand the meaning of the actions, you have to look at the preconditions but also the invariant of the box.
e.g. it is not necessary to require that the current value is > the inserted value in gap2, because the invariant says that the result must be sorted.
therefore, it is impossible to perform the action anyway. 
This is a bit confusing. 

*/

/*@

//TODO: The following is a workaround because the theory concerning malloc fails to prove that
//  malloc_block_llnode_ex(n) &*& malloc_block_llnode_ex(n) is impossible

predicate malloc_block_llnode_ex(struct llnode* node;) =
    malloc_block_llnode(node) &*&
    node->malloc_ex |-> _;

lemma void malloc_block_llnode_ex_distinct(struct llnode *n1, struct llnode *n2)
    requires malloc_block_llnode_ex(n1) &*& malloc_block_llnode_ex(n2);
    ensures malloc_block_llnode_ex(n1) &*& malloc_block_llnode_ex(n2) &*& n1 != n2;
{
    open malloc_block_llnode_ex(n1);
    open malloc_block_llnode_ex(n2);
    close malloc_block_llnode_ex(n1);
    close malloc_block_llnode_ex(n2);
}   
 
predicate node_internal(struct llnode *node; struct mutex3 *mutex, int value, int owner) =
    node != 0 &*&
    malloc_block_llnode_ex(node) &*&
    [1/3]node->value |-> value &*&
    [1/3]node->mutex |-> mutex &*&
    [1/2]node->owner |-> owner;

predicate link_internal(struct llnode *node; struct mutex3* mutex, struct llnode *next, int value, int owner, struct mutex3* nmutex, int nvalue) = 
    node != 0 &*&
    [1/3]node->mutex |-> mutex  &*&
    [1/3]node->value |-> value &*&
    [1/2]node->owner |-> owner &*&
    node->next |-> next &*& 
    (next == 0 ? nmutex == 0 &*& nvalue == 0 : [1/3]next->mutex |-> nmutex &*& mutex3(nmutex) &*& [1/3]next->value |-> nvalue);

predicate link(struct llnode *node; struct llnode *next, int value, int owner) = 
    link_internal(node, _, next, value, owner, _, _); 

predicate linkex(struct llnode *node; struct mutex3* mutex, struct llnode *next, int value, int owner, struct mutex3* nmutex, int nvalue) = 
    link_internal(node, mutex, next, value, owner, nmutex, nvalue) &*& next != 0; 

predicate linkex2(struct llnode *node; struct mutex3* mutex, struct llnode *next, int value, int owner) = 
    link_internal(node, mutex, next, value, owner, _, _);

lemma void link_internal_distinct(struct llnode *n1, struct llnode *n2) 
    requires link_internal(n1, ?n1m, ?n1n, ?n1v, ?o1, ?n1nm, ?n1nv) &*& link_internal(n2, ?n2m, ?n2n, ?n2v, ?o2, ?n2nm, ?n2nv);
    ensures link_internal(n1, n1m, n1n, n1v, o1, n1nm, n1nv) &*& link_internal(n2, n2m, n2n, n2v, o2, n2nm, n2nv) &*& n1 != n2;
{
    open link_internal(n1, n1m, n1n, n1v, o1, n1nm, n1nv);
    open link_internal(n2, n2m, n2n, n2v, o2, n2nm, n2nv);
    close link_internal(n1, n1m, n1n, n1v, o1, n1nm, n1nv);
    close link_internal(n2, n2m, n2n, n2v, o2, n2nm, n2nv);
}

lemma void link_internal_node_internal_match(struct llnode *n)
    requires node_internal(n, ?nm, ?nv, ?no) &*& link_internal(n, ?nm2, ?nn, ?nv2, ?no2, ?nnm, ?nnv);
    ensures node_internal(n, nm, nv, no) &*& link_internal(n, nm2, nn, nv2, no2, nnm, nnv) &*& nm == nm2 &*& nv == nv2 &*& no == no2;
{
    open node_internal(n, nm, nv, no);
    open link_internal(n, nm2, nn, nv2, no2, nnm, nnv);
    close node_internal(n, nm, nv, no);
    close link_internal(n, nm2, nn, nv2, no2, nnm, nnv);
}

lemma void link_internal_node_internal_match2(struct llnode *n)
    requires node_internal(n, ?nm, ?nv, ?no) &*& link_internal(?p, ?pm, n, ?pv, ?po, ?nm2, ?nv2) &*& n!=0;
    ensures node_internal(n, nm, nv, no) &*& link_internal(p, pm, n, pv, po, nm2, nv2) &*& nm == nm2 &*& nv == nv2;
{
    open node_internal(n, nm, nv, no);
    open link_internal(p, pm, n, pv, po, nm2, nv2);
    close node_internal(n, nm, nv, no);
    close link_internal(p, pm, n, pv, po, nm2, nv2);
}

lemma void linkex_distinct(struct llnode *n1, struct llnode *n2) 
    requires linkex(n1, ?n1m, ?n1n, ?n1v, ?n1nm, ?n1nv, ?o1) &*& linkex(n2, ?n2m, ?n2n, ?n2v, ?n2nm, ?n2nv, ?o2);
    ensures linkex(n1, n1m, n1n, n1v, n1nm, n1nv, o1) &*& linkex(n2, n2m, n2n, n2v, n2nm, n2nv, o2) &*& n1 != n2;
{
    link_internal_distinct(n1, n2);
}


predicate freenode(struct llnode *node; struct llnode *next, int value) =
    node_internal(node, ?mutex, value, INT_MIN) &*&
    link(node, next, value, INT_MIN);

predicate lockednode(struct llnode *node; int value, int owner) =
    node_internal(node, ?mutex, value, owner) &*&
    mutex3_held(mutex);

predicate unknownnode(struct llnode *node, struct llnode *next, int value, int owner) =
    (owner != INT_MIN ? lockednode(node, value, owner) : freenode(node, next, value));

predicate node(struct llnode *node, struct mutex3* mutex, struct llnode *next, int value, int owner) =
    node_internal(node, mutex, value, owner) &*&
    (owner != INT_MIN ? mutex3_held(mutex) : link_internal(node, mutex, next, value, owner, _, _));

lemma void unknownnode_notnil(struct llnode* node)
    requires unknownnode(node, ?next, ?value, ?locked);
    ensures unknownnode(node, next, value, locked) &*& node != 0;
{
    open unknownnode(node, next, value, locked);
    open node_internal(node, ?m, value, locked);
    close node_internal(node, m, value, locked);
    close unknownnode(node, next, value, locked);
}

lemma void convert_unknownnode_mutexheld(struct llnode *node) 
   requires [?f]node->mutex |-> ?mutex &*& mutex3_held(mutex) &*& unknownnode(node, ?next, ?value, ?owner);
   ensures [f]node->mutex |-> mutex &*& mutex3_held(mutex) &*& unknownnode(node, next, value, owner) &*& owner == INT_MIN;
{
    open unknownnode(node, next, value, owner);
    open node_internal(node, _, value, owner);
    close node_internal(node, _, value, owner);
    if(owner != INT_MIN) mutex3_exclusive(mutex);
    close unknownnode(node, next, value, owner);
}
lemma void lock_freenode(struct llnode *node, int owner) 
    requires [?f]node->mutex |-> ?mutex &*& mutex3_held(mutex) &*& freenode(node, ?next, ?value);
    ensures [f]node->mutex |-> mutex &*& lockednode(node, value, owner) &*& link(node, next, value, owner);
{
    open freenode(node, next, value);
    open node_internal(node, _, value, INT_MIN);
    node->owner = owner;
    close node_internal(node, mutex, value, owner);
}
lemma void unlock_lockednode(struct llnode *node, struct llnode *next, int value) 
    requires linkex2(node, ?mutex, next, _, _) &*& lockednode(node, value, _);
    ensures mutex3_held(mutex) &*& freenode(node, next, value);
{
    open linkex2(node, mutex, next, ?value2, ?owner);
    open lockednode(node, value, ?owner2);
    open node_internal(node, _, value, owner2);
    node->owner = INT_MIN;
    close node_internal(node, mutex, value, INT_MIN);
    close link(node, next, value, INT_MIN);
    close freenode(node, next, value);
}


lemma void node_internal_distinct(struct llnode *n1, struct llnode *n2)
    requires node_internal(n1, ?m1, ?v1, ?o1) &*& node_internal(n2, ?m2, ?v2, ?o2);
    ensures node_internal(n1, m1, v1, o1) &*& node_internal(n2, m2, v2, o2) &*& n1 != n2;
{
    open node_internal(n1, m1, v1, o1);
    open node_internal(n2, m2, v2, o2);
    malloc_block_llnode_ex_distinct(n1, n2);
    close node_internal(n1, m1, v1, o1);
    close node_internal(n2, m2, v2, o2);
}

lemma void unknownnode_distinct(struct llnode *node1, struct llnode *node2)
    requires unknownnode(node1, ?next1, ?value1, ?locked1) &*& unknownnode(node2, ?next2, ?value2, ?locked2);
    ensures unknownnode(node1, next1, value1, locked1) &*& unknownnode(node2, next2, value2, locked2) &*& node1 != node2;
{
    open unknownnode(node1, next1, value1, locked1);
    if(locked1 != INT_MIN) open lockednode(node1, value1, locked1); else open freenode(node1, next1, value1);
    open unknownnode(node2, next2, value2, locked2);
    if(locked2 != INT_MIN) open lockednode(node2, value2, locked2); else open freenode(node2, next2, value2);
    node_internal_distinct(node1, node2);
    if(locked1 != INT_MIN) close lockednode(node1, value1, locked1); else close freenode(node1, next1, value1);
    close unknownnode(node1, next1, value1, locked1);
    if(locked2 != INT_MIN) close lockednode(node2, value2, locked2); else close freenode(node2, next2, value2);
    close unknownnode(node2, next2, value2, locked2);
}



inductive gnode = gnode(struct llnode *, struct llnode *, int, int);

fixpoint struct llnode* gnode_node(gnode gn) { switch(gn) { case gnode(node, next, value, owner): return node; } }
fixpoint struct llnode* gnode_next(gnode gn) { switch(gn) { case gnode(node, next, value, owner): return next; } }
fixpoint int gnode_value(gnode gn) { switch(gn) { case gnode(node, next, value, owner): return value; } }
fixpoint int gnode_owner(gnode gn) { switch(gn) { case gnode(node, next, value, owner): return owner; } }


// ghost linked list segment with gaps
// either empty, or node, next, value, lockedBy (the value which has reserved this node)
        
predicate lsg(struct llnode *from, struct llnode *to, list<gnode> gnodes) =
    switch(gnodes) {
        case nil: return from == to;
        case cons(gn, gnodes2):
        return switch(gn) {
            case gnode(node, next, value, owner):
                return 
                    node == from &*& 
                    from != to &*&
                    unknownnode(node, next, value, owner) &*&
                    lsg(next, to, gnodes2);
        };
    };

lemma void unknownnode_lsg_distinct(struct llnode* node, struct llnode* from, struct llnode* to, list<gnode> gnodes)
    requires unknownnode(node, ?next, ?value, ?locked) &*& lsg(from, to, gnodes);
    ensures unknownnode(node, next, value, locked) &*& lsg(from, to, gnodes) &*& !wfmap_contains_key(gnodes, gnode_node, node);
{
    switch(gnodes) {
        case nil:
            open lsg(from, to, gnodes);
            close lsg(from, to, gnodes);
        case cons(gn, gnodes2):
            open lsg(from, to, gnodes);
            assert unknownnode(from, ?next2, ?value2, ?locked2);
            unknownnode_distinct(node, from);
            unknownnode_lsg_distinct(node, next2, to, gnodes2);
            close lsg(from, to, gnodes);
    }
}

lemma void lsg_gnodes_wfmap(struct llnode *from, struct llnode *to, list<gnode> gnodes) 
    requires lsg(from, to, gnodes);
    ensures lsg(from, to, gnodes) &*& is_wfmap(gnodes, gnode_node)==true;
{
    switch(gnodes) {
        case nil: 
        case cons(gn, gnodes2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            open lsg(from, to, gnodes);
            unknownnode_lsg_distinct(from, gnnext, to, gnodes2);
            lsg_gnodes_wfmap(gnnext, to, gnodes2);
            close lsg(from, to, gnodes);    
        }
    }
}


predicate lgn_contains(list<gnode> gnodes, struct llnode* node, struct llnode* next, int value, int owner) =
    mem(gnode(node, next, value, owner), gnodes) == true;

fixpoint list<int> lgn_values(list<gnode> gnodes) 
{
    return map(gnode_value, gnodes);
    /*switch(gnodes) {
        case nil: return nil;
        case cons(gn, tail): return cons(gnode_value(gn), lgn_values(tail));
    }*/
}    

fixpoint bool gn_owner_equals(gnode n, int owner) 
{
    return gnode_owner(n) == owner;
}

fixpoint list<gnode> lgn_filterowner(list<gnode> gnodes, int owner) 
{
    return set_filter2(gnodes, gn_owner_equals, owner);
    /*
    switch(gnodes) {
        case nil: return nil;
        case cons(gn, tail): return gnode_owner(gn) == owner ? cons(gn, lgn_filterowner(tail, owner)) : lgn_filterowner(tail, owner);
    }*/
}

fixpoint bool lgn_contains_freenode(list<gnode> gnodes, struct llnode* node) {
    switch(gnodes) {
        case nil: return false;
        case cons(gn, tail): return gnode_node(gn) == node ? gnode_owner(gn) == INT_MIN : lgn_contains_freenode(tail, node);
    }
}

lemma void lgn_contains_freenode_true(list<gnode> gnodes, struct llnode* node)
    requires lgn_contains_freenode(gnodes, node)==true;
    ensures lgn_contains(gnodes, node, ?next, ?value, INT_MIN);
{
    switch(gnodes) {
        case nil: 
        case cons(gn, tail): 
        switch(gn) {
            case gnode(node2, next2, value2, owner2):
                if(node2 != node)  {
                     lgn_contains_freenode_true(tail, node);
                     open lgn_contains(tail, node, ?nn, ?nv, INT_MIN);
                     close lgn_contains(gnodes, node, nn, nv, INT_MIN);
                } else {
                     close lgn_contains(gnodes, node, next2, value2, INT_MIN); 
                }
        }
    }
}
lemma void lgn_contains_freenode_append(list<gnode> gns1, list<gnode> gns2, struct llnode* node)
    requires true;
    ensures lgn_contains_freenode(append(gns1, gns2), node) == lgn_contains_freenode(gns1, node) || lgn_contains_freenode(gns2, node);
{
    switch(gns1) {
        case nil:
        case cons(h,t):
            lgn_contains_freenode_append(t, gns2, node);
    }
}

fixpoint bool lgn_contains_fullnode(list<gnode> gnodes, struct llnode* node, struct llnode* next, int value, int owner) {
    return mem(gnode(node, next, value, owner), gnodes);
    /*switch(gnodes) {
        case nil: return false;
        case cons(gn, tail): return
        switch(gn) {
            case gnode(node2, next2, value2, owner2):
                return node == node2 ? next == next2 && value == value2 && owner == owner2 : lgn_contains_fullnode(tail, node, next, value, owner);
        };
    }*/
}

fixpoint bool lgn_contains_node(list<gnode> gnodes, struct llnode* node)
{
    return wfmap_contains_key(gnodes, gnode_node, node);
    /*switch(gnodes) {
        case nil: return false;
        case cons(gn, tail): return gnode_node(gn) == node || lgn_contains_node(tail, node);
    }*/
}

lemma void lgn_contains_node_true(list<gnode> gnodes, struct llnode* node)
    requires lgn_contains_node(gnodes, node)==true;
    ensures lgn_contains(gnodes, node, ?next, ?value, ?owner);
{
    switch(gnodes) {
        case nil: 
        case cons(gn, tail): 
        switch(gn) {
            case gnode(node2, next2, value2, owner2):
                if(node2 != node)  {
                     lgn_contains_node_true(tail, node);
                     open lgn_contains(tail, node, ?nn, ?nv, ?no);
                     close lgn_contains(gnodes, node, nn, nv, no);
                } else {
                     close lgn_contains(gnodes, node, next2, value2, owner2); 
                }
        }
    }
}

lemma void not_contains_node_not_mem(list<gnode> gnodes, struct llnode* node, struct llnode* next, int value, int owner)
    requires !lgn_contains_node(gnodes, node);
    ensures !mem(gnode(node, next, value, owner), gnodes);
{
    switch(gnodes) {
        case nil:
        case cons(gn, gnodes2):
            not_contains_node_not_mem(gnodes2, node, next, value, owner);
    }
}


fixpoint bool is_wflgn(struct llnode* from, struct llnode* to, list<gnode> gnodes) 
{
    switch(gnodes) {
        case nil: return from == to;
        case cons(gn, gnodes2): return
        switch(gn) {
            case gnode(node, next, value, owner):
                return node != 0 && node == from && !wfmap_contains_key(gnodes2, gnode_node, node) && is_wflgn(next, to, gnodes2);
        };
    }    
}
lemma void lsg_gnodes_is_wflgn(struct llnode* from, struct llnode* to, list<gnode> gnodes) 
    requires lsg(from, to, gnodes);
    ensures lsg(from, to, gnodes) &*& is_wflgn(from, to, gnodes) == true;
{
    open lsg(from, to, gnodes);
    switch(gnodes) {
        case nil: 
        case cons(gn, gnodes2): 
        switch(gn) {
            case gnode(node, next, value, owner):
            lsg_gnodes_is_wflgn(next, to, gnodes2);
            unknownnode_lsg_distinct(node, next, to, gnodes2);
            unknownnode_notnil(node);
            assert node != 0 &*& node == from;
        }
    }       
    close lsg(from, to, gnodes);
}
lemma void lsg_gnodes_is_wflgn_helper(struct llnode* from) 
    requires lsg(from, 0, ?gnodes) &*& from != 0;
    ensures lsg(from, 0, gnodes) &*& is_wflgn(from, 0, gnodes) == true &*& gnode_node(head(gnodes)) == from;
{
    lsg_gnodes_is_wflgn(from, 0, gnodes);
    open lsg(from, 0, gnodes);
    
    close lsg(from, 0, gnodes);
}

fixpoint int lgn_get_value(list<gnode> gnodes, struct llnode* node) 
{
    return gnode_value(wfmap_get(gnodes, gnode_node, node));
}

predicate gres<t>(t res;) = true;
predicate gres2<t1, t2>(t1 res1, t2 res2;) = true;
predicate gres3<t1, t2, t3>(t1 res1, t2 res2, t3 res3;) = true;

lemma void list_split<t>(list<t> l, t v)
    requires mem(v, l)==true;
    ensures gres2(?l1, ?l2) &*& l == append(l1, cons(v, l2)) &*& !mem(v, l1);
{
    switch(l) {
        case nil:
        case cons(h,t):
            if(h==v) {
                close gres2(nil, t);
            } else {
                list_split(t, v);
                open gres2(?t1, ?t2);
                close gres2(cons(h, t1), t2);
            }
    }
}
lemma void list_equality_helper<t>(list<t> l1, list<t> l2, list<t> l3, list<t> l4, t v)
    requires append(l1, cons(v, l2)) == append(l3, cons(v, l4)) &*& !mem(v, l1) &*& !mem(v, l3);
    ensures l1 == l3 &*& l2 == l4;
{
    switch(l1) {
        case nil: switch(l3) { case nil: case cons(l3h, l3t): }
        case cons(l1h, l1t):
            switch(l3) { 
                case nil: 
                case cons(l3h, l3t): 
                    list_equality_helper(l1t, l2, l3t, l4, v);
            }
    }
}

lemma void unknownnode_lsg_distinct_old(struct llnode* node, struct llnode* from, struct llnode* to, list<gnode> gnodes)
    requires unknownnode(node, ?next, ?value, ?locked) &*& lsg(from, to, gnodes);
    ensures unknownnode(node, next, value, locked) &*& lsg(from, to, gnodes) &*& !lgn_contains_node(gnodes, node);
{
    switch(gnodes) {
        case nil:
            open lsg(from, to, gnodes);
            close lsg(from, to, gnodes);
        case cons(gn, gnodes2):
            open lsg(from, to, gnodes);
            assert unknownnode(from, ?next2, ?value2, ?locked2);
            unknownnode_distinct(node, from);
            unknownnode_lsg_distinct_old(node, next2, to, gnodes2);
            close lsg(from, to, gnodes);
    }
}

lemma void lsg_split(struct llnode* from, list<gnode> gns, struct llnode* node) 
    requires 
        lsg(from, 0, gns) &*&
        lgn_contains(gns, node, ?next, ?value, ?owner);
    ensures 
        lsg(from, node, ?gns1) &*&  
        unknownnode(node, next, value, owner) &*&
        lsg(next, 0, ?gns2) &*&
        !lgn_contains_node(gns1, node) &*&
        !lgn_contains_node(gns2, node) &*&
        gns == append(gns1, cons(gnode(node, next, value, owner), gns2));
{
    open lgn_contains(gns, node, next, value, owner);
    switch(gns) {
        case nil:
        case cons(gn, gnst):
        switch(gn) {
            case gnode(gn_node, gn_next, gn_value, gn_owner):
            open lsg(from, 0, gns);
            if(gn_node == node) {
                unknownnode_lsg_distinct(from, gn_next, 0, gnst);
                not_contains_node_not_mem(gnst, node, next, value, owner);
                assert gn_next == next &*& gn_value == value &*& gn_owner == owner;
                close lsg(from, from, nil);
            } else {
                close lgn_contains(gnst, node, next, value, owner);
                lsg_split(gn_next, gnst, node);
                assert lsg(gn_next, node, ?gnst1);
                close lsg(from, node, cons(gn, gnst1));
            }
        }
    }
}

lemma void lsg_split_old(struct llnode* from, list<gnode> gns, struct llnode* node) 
    requires 
        lsg(from, 0, gns) &*&
        lgn_contains_node(gns, node) == true;
    ensures 
        lsg(from, node, ?gns1) &*&  
        lsg(node, 0, ?gns2) &*&
        !lgn_contains_node(gns1, node) &*&
        gns == append(gns1, gns2);
{
    switch(gns) {
        case nil:
        case cons(gn, gnst):
        switch(gn) {
            case gnode(gn_node, gn_next, gn_value, gn_owner):
            open lsg(from, 0, gns);
            if(gn_node == node) {
                close lsg(from, from, nil);
                close lsg(from, 0, gns);
            } else {
                lsg_split_old(gn_next, gnst, node);
                assert lsg(gn_next, node, ?gnst1);
                close lsg(from, node, cons(gn, gnst1));
            }
        }
    }
}


lemma void lsg_append(struct llnode* from, struct llnode* node, list<gnode> gns1, list<gnode> gns2) 
    requires 
        lsg(from, node, gns1) &*&  
        lsg(node, 0, gns2);
    ensures 
        lsg(from, 0, append(gns1, gns2));
{
    switch(gns1) {
        case nil: 
            open lsg(from, node, gns1);
            
        case cons(gn, gnst):
        switch(gn) {
            case gnode(gn_node, gn_next, gn_value, gn_owner):
            open lsg(from, node, gns1);
            lsg_append(gn_next, node, gnst, gns2);
            unknownnode_notnil(from);
            close lsg(from, 0, cons(gn, append(gnst, gns2)));
        }
    }
}
lemma void lsg_openex(struct llnode* from, struct llnode* to, list<gnode> gns) 
    requires lsg(from, to, gns) &*& from != to; 
    ensures unknownnode(from, ?next, ?value, ?owner) &*& lsg(next, to, ?gns2) &*& 
        gns == cons(gnode(from, next, value, owner), gns2) &*& !lgn_contains_node(gns2, from);
{
    open lsg(from, to, gns);
    switch(gns) {
        case nil: assert false;
        case cons(gn, gnst): 
        switch(gn) {
            case gnode(n, nn, nv, no): 
                unknownnode_lsg_distinct(from, nn, to, gnst);
        }
    }
}
fixpoint list<int> lgn_owners(list<gnode> gnodes) 
{
    return set_map(gnodes, gnode_owner);
}
fixpoint bool ownedOk(list<gnode> gnodes, list<int> reserved) 
{
    return set_subset(lgn_owners(gnodes), set_add(reserved, INT_MIN));
}


lemma void lgn_owners_filterowner_notempty(list<gnode> gnodes, int owner) 
    requires owner != INT_MIN; 
    ensures mem(owner, lgn_owners(gnodes)) == (lgn_filterowner(gnodes, owner) != set_empty());
{
    switch(gnodes) {
        case nil:
        case cons(h, t):
            lgn_owners_filterowner_notempty(t, owner);
    }
}


fixpoint gnode updateNodeOwner(gnode gn, int owner)
{
    switch(gn) {
        case gnode(node, next, value, o) : return gnode(node, next, value, owner);
    }
}

fixpoint list<gnode> updateOwner(list<gnode> gnodes, struct llnode* node, int owner) 
{
    switch(gnodes) {
        case nil: return nil;
        case cons(gn, tail):
            return (node == gnode_node(gn) ? cons(updateNodeOwner(gn, owner), updateOwner(tail, node, owner)) : cons(gn, updateOwner(tail, node, owner)));
    }
}

lemma void updateOwner_append(list<gnode> gns1, list<gnode> gns2, struct llnode* node, int newOwner)
    requires true;
    ensures updateOwner(append(gns1, gns2), node, newOwner) == append(updateOwner(gns1, node, newOwner), updateOwner(gns2, node, newOwner));
{
    switch(gns1) {
        case nil:
        case cons(h, t):
            updateOwner_append(t, gns2, node, newOwner);
    }
}
lemma void updateOwner_invariant(list<gnode> gnodes, struct llnode* node, int newOwner)
    requires !lgn_contains_node(gnodes, node);
    ensures updateOwner(gnodes, node, newOwner) == gnodes;
{
    switch(gnodes) {
        case nil: 
        case cons(gn, tail):
            updateOwner_invariant(tail, node, newOwner);
    }    
}

lemma void lgn_filterowner_spec(list<gnode> gnodes, gnode gn, int owner) 
    requires true;
    ensures mem(gn, lgn_filterowner(gnodes, owner)) == ((gnode_owner(gn) == owner) && mem(gn, gnodes));
{
    set_filter2_spec(gnodes, gn_owner_equals, owner, gn);
}

lemma void lgn_filterowner_append(list<gnode> gns1, list<gnode> gns2, int owner)
    requires true;
    ensures lgn_filterowner(append(gns1, gns2), owner) == append(lgn_filterowner(gns1, owner), lgn_filterowner(gns2, owner));
{
    switch(gns1) {
        case nil:
        case cons(h, t):
            lgn_filterowner_append(t, gns2, owner);
    }
}
lemma void lgn_filterowner_subset(list<gnode> gns, int owner)
    requires true;
    ensures set_subset(lgn_filterowner(gns, owner), gns) == true;
{
    switch(gns) {
        case nil:
        case cons(h, t):
            lgn_filterowner_subset(t, owner);
            set_subset_set_add(lgn_filterowner(t, owner), h, t);
    }
}

//TODO: implement wfmap_containskey using list_exists. Then it is possible to create general lemma for relation between exists and filter.
lemma void lgn_filterowner_not_contains_node(list<gnode> gns, int owner, struct llnode* node)
    requires !lgn_contains_node(gns, node);
    ensures !lgn_contains_node(lgn_filterowner(gns, owner), node);
{
    switch(gns) {
        case nil:
        case cons(h, t):
             lgn_filterowner_not_contains_node(t, owner, node);
    }
}

lemma void updateOwner_standard(list<gnode> gns1, struct llnode* node, struct llnode* next, int value, int owner, list<gnode> gns2, int newOwner)
    requires !lgn_contains_node(gns1, node) &*& !lgn_contains_node(gns2, node);
    ensures updateOwner(append(gns1, cons(gnode(node, next, value, owner), gns2)), node, newOwner) == append(gns1, cons(gnode(node, next, value, newOwner), gns2)); 
{
    updateOwner_append(gns1, cons(gnode(node, next, value, owner), gns2), node, newOwner);
    updateOwner_invariant(gns1, node, newOwner);
    updateOwner_invariant(gns2, node, newOwner);
}

lemma void updateOwner_lgn_filterowner_otherOwner(list<gnode> gns1, struct llnode* node, struct llnode* next, int value, int owner, list<gnode> gns2, int newOwner, int otherOwner)
    requires !lgn_contains_node(gns1, node) &*& !lgn_contains_node(gns2, node) &*& otherOwner != owner &*& otherOwner != newOwner;
    ensures lgn_filterowner(updateOwner(append(gns1, cons(gnode(node, next, value, owner), gns2)), node, newOwner), otherOwner) == 
            lgn_filterowner(append(gns1, cons(gnode(node, next, value, owner), gns2)), otherOwner);
{
    updateOwner_standard(gns1, node, next, value, owner, gns2, newOwner);
    lgn_filterowner_append(gns1, cons(gnode(node, next, value, newOwner), gns2), otherOwner);
    lgn_filterowner_append(gns1, cons(gnode(node, next, value, owner), gns2), otherOwner);
}


lemma void lock_freenode_otherowner(list<gnode> gnodes, struct llnode* node, int newOwner, int otherOwner)
    requires is_wfmap(gnodes, gnode_node)==true &*& lgn_contains_freenode(gnodes, node) == true &*& newOwner != otherOwner &*& otherOwner != INT_MIN;
    ensures lgn_filterowner(updateOwner(gnodes, node, newOwner), otherOwner) == lgn_filterowner(gnodes, otherOwner);
{
    switch(gnodes) {
        case nil:
        case cons(h, t):
        switch(h) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            if(gnnode == node) {
                updateOwner_invariant(t, node, newOwner);
            } else {
                lock_freenode_otherowner(t, node, newOwner, otherOwner);
            }
        }
    }
}

lemma void free_lockednode_otherowner(list<gnode> gnodes, struct llnode* node, struct llnode* next, int value, int owner, int otherOwner)
    requires is_wfmap(gnodes, gnode_node)==true &*& lgn_contains_fullnode(gnodes, node, next, value, owner) == true &*& owner != INT_MIN &*& owner != otherOwner &*& otherOwner != INT_MIN;
    ensures lgn_filterowner(updateOwner(gnodes, node, INT_MIN), otherOwner) == lgn_filterowner(gnodes, otherOwner);
{
    switch(gnodes) {
        case nil:
        case cons(h, t):
        switch(h) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            if(gnnode == node) {
                wfmap_contains_equal(gnodes, gnode_node, gnode(gnnode, gnnext, gnvalue, gnowner), gnode(node, next, value, owner));
                assert gnnext == next &*& gnvalue == value &*& gnowner == owner;
                updateOwner_invariant(t, node, INT_MIN);
            } else {
                free_lockednode_otherowner(t, node, next, value, owner, otherOwner);
            }
        }
    }
}

lemma void updateOwner_maintains_values(list<gnode> gnodes, struct llnode* node, int owner)
    requires true;
    ensures lgn_values(updateOwner(gnodes, node, owner)) == lgn_values(gnodes);
{
    switch(gnodes) {
        case nil:
        case cons(gn,t): 
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
                updateOwner_maintains_values(t, node, owner);
        }
    }
}

lemma void lsg_contains_head(struct llnode *from, list<gnode> gnodes)
    requires lsg(from, 0, gnodes) &*& from != 0;
    ensures lsg(from, 0, gnodes) &*& lgn_contains_node(gnodes, from) == true;
{
    open lsg(from, 0, gnodes);
    close lsg(from, 0, gnodes);
}
lemma void lsg_contains_next(struct llnode *from, list<gnode> gnodes, struct llnode* node, struct llnode* next, int value, int owner)
    requires lsg(from, 0, gnodes) &*& lgn_contains_fullnode(gnodes, node, next, value, owner) == true &*& next != 0;
    ensures lsg(from, 0, gnodes) &*& lgn_contains_node(gnodes, next) == true;
{
    switch(gnodes) {
        case nil:
        case cons(h, t):
        switch(h) {
            case gnode(node2, next2, value2, owner2):
            lsg_gnodes_wfmap(from, 0, gnodes);
            open lsg(from, 0, gnodes);
            if(node2 == node) {
                wfmap_contains_equal(gnodes, gnode_node, gnode(node2, next2, value2, owner2), gnode(node, next, value, owner));
                unknownnode_lsg_distinct(from, next, 0, t);
                assert next == next2 &*& value == value2 &*& owner == owner2;
                open lsg(next2, 0, t);
                close lsg(next2, 0, t);
            } else {
                lsg_contains_next(next2, t, node, next, value, owner);
            }
            close lsg(from, 0, gnodes);
        } 
        
    }
}

    
lemma void lsg_locknode(struct llnode *from, list<gnode> gnodes, struct llnode *node, int owner)
    requires 
        [?f]node->mutex |-> ?mutex &*& mutex3_held(mutex) &*& 
        [?f2]node->value |-> ?value &*& value < INT_MAX &*&
        lsg(from, 0, gnodes) &*& 
        last(lgn_values(gnodes)) == INT_MAX &*&
        lgn_contains_node(gnodes, node) == true &*& 
        owner != INT_MIN;
    ensures 
        [f]node->mutex |-> mutex &*& 
        [f2]node->value |-> value &*&
        linkex(node, mutex, ?next, value, owner, ?nextmutex, ?nextvalue) &*&
        lsg(from, 0, updateOwner(gnodes, node, owner)) &*&
        is_wfmap(updateOwner(gnodes, node, owner), gnode_node)==true &*&
        lgn_contains_freenode(gnodes, node) == true &*&
        lgn_values(updateOwner(gnodes, node, owner)) == lgn_values(gnodes) &*&
        set_subset(lgn_owners(updateOwner(gnodes, node, owner)), set_add(lgn_owners(gnodes), owner)) == true &*&
        set_equals(lgn_filterowner(updateOwner(gnodes, node, owner), owner), set_add(lgn_filterowner(gnodes, owner), gnode(node, next, value, owner))) == true;
{
    switch(gnodes) {
    case nil:
    case cons(gn, gnodes2):
        switch(gn) {
        case gnode(gnnode, gnnext, gnvalue, gnowner):
            open lsg(from, 0, gnodes);
            if(from == node) {
                convert_unknownnode_mutexheld(node);
                open unknownnode(node, gnnext, gnvalue, gnowner);
                lock_freenode(node, owner);
                
                open node_internal(node, ?nodemutex, gnvalue, owner);
                assert gnvalue == value;
                close node_internal(node, mutex, value, owner);
                
                close unknownnode(node, gnnext, gnvalue, owner);
                unknownnode_lsg_distinct(from, gnnext, 0, gnodes2);
                updateOwner_invariant(gnodes2, node, owner);
                if(gnnext == 0) {
                    open lsg(gnnext, 0, gnodes2);
                    assert false;
                }
                open link(node, gnnext, gnvalue, owner);
                close link_internal(node, mutex, gnnext, gnvalue, owner, _, _);
                close linkex(node, mutex, gnnext, gnvalue, owner, _, _);
                assert updateOwner(gnodes2, node, owner) == gnodes2;
                assert lgn_owners(updateOwner(gnodes, node, owner)) == cons(owner, lgn_owners(gnodes2));
                assert lgn_filterowner(gnodes, owner) == lgn_filterowner(gnodes2, owner);
                assert lgn_filterowner(updateOwner(gnodes, node, owner), owner) == cons(gnode(node, gnnext, value, owner), lgn_filterowner(gnodes2, owner));
                assert set_add(lgn_filterowner(gnodes, owner), gnode(node, gnnext, value, owner)) == cons(gnode(node, gnnext, value, owner), lgn_filterowner(gnodes2, owner));
                set_equals_refl(lgn_filterowner(updateOwner(gnodes, node, owner), owner));
                assert lgn_owners(updateOwner(gnodes, node, owner)) == cons(owner, lgn_owners(gnodes2));
                assert lgn_owners(gnodes) == cons(INT_MIN, lgn_owners(gnodes2));
                set_add_assoc(lgn_owners(gnodes2), INT_MIN, owner);
                assert set_equals(cons(INT_MIN, cons(owner, lgn_owners(gnodes2))), cons(owner, cons(INT_MIN, lgn_owners(gnodes2)))) == true;
                assert set_subset(lgn_owners(updateOwner(gnodes, node, owner)), set_add(lgn_owners(gnodes), owner)) == true;
            } else {
                if(gnnext == 0) {
                    open lsg(gnnext, 0, gnodes2);
                    assert false;
                }
                switch(gnodes2) { case nil: case cons(gns2h, gns2t): } //to assure that the last node of gnodes2 has value INT_MAX
                lsg_locknode(gnnext, gnodes2, node, owner);
                assert linkex(node, mutex, ?next, value, owner, ?nmutex, ?nvalue);
                if(gnowner == owner) {
                    list<gnode> gns1 = lgn_filterowner(updateOwner(gnodes2, node, owner), owner);
                    list<gnode> gns2 = lgn_filterowner(gnodes2, owner);
                    gnode ugn = gnode(node, next, value, owner);
                    assert set_equals(gns1, set_add(gns2, ugn)) == true;
                    list<gnode> gns3 = lgn_filterowner(updateOwner(gnodes, node, owner), owner);
                    list<gnode> gns4 = lgn_filterowner(gnodes, owner);
                    assert gns3 == set_add(gns1, gn);
                    assert gns4 == set_add(gns2, gn);
                    set_equals_add_both(gns1, set_add(gns2, ugn), gn);
                    assert set_equals(set_add(gns1, gn), set_add(set_add(gns2, ugn), gn)) == true;
                    set_add_assoc(gns2, ugn, gn);
                    assert set_equals(set_add(set_add(gns2, ugn), gn), set_add(set_add(gns2, gn), ugn)) == true;
                    set_equals_transitive(set_add(gns1, gn), set_add(set_add(gns2, ugn), gn), set_add(set_add(gns2, gn), ugn));
                    assert set_equals(set_add(gns1, gn), set_add(set_add(gns2, gn), ugn)) == true;
                    assert set_equals(gns3, set_add(gns4, ugn)) == true;
                }
                assert set_subset(lgn_owners(updateOwner(gnodes2, node, owner)), set_add(lgn_owners(gnodes2), owner)) == true;
                set_subset_add_both(lgn_owners(updateOwner(gnodes2, node, owner)), set_add(lgn_owners(gnodes2), owner), gnowner);
                set_add_assoc(lgn_owners(gnodes2), owner, gnowner);
                set_subset_equals_r(lgn_owners(updateOwner(gnodes, node, owner)), set_add(set_add(lgn_owners(gnodes2), owner), gnowner), set_add(set_add(lgn_owners(gnodes2), gnowner), owner));
                assert set_subset(lgn_owners(updateOwner(gnodes, node, owner)), set_add(lgn_owners(gnodes), owner)) == true;
            }
            close lsg(from, 0, updateOwner(gnodes, node, owner));
            lsg_gnodes_wfmap(from, 0, updateOwner(gnodes, node, owner));
        }
    }
}


lemma void lsg_gap1_helper(struct llnode *from, list<gnode> gnodes, struct llnode *node, struct llnode *next, int value, int owner)
    requires 
        linkex(node, ?mutex, next, value, owner, ?nextmutex, ?nextvalue) &*&
        lsg(from, 0, gnodes) &*& 
        mem(gnode(node, next, value, owner), gnodes) == true &*& 
        owner != INT_MIN;
    ensures 
        lsg(from, 0, updateOwner(gnodes, node, INT_MIN)) &*&
        mutex3_held(mutex) &*&
        is_wfmap(updateOwner(gnodes, node, INT_MIN), gnode_node)==true &*&
        lgn_values(updateOwner(gnodes, node, INT_MIN)) == lgn_values(gnodes) &*&
        set_subset(lgn_owners(updateOwner(gnodes, node, INT_MIN)), set_add(lgn_owners(gnodes), INT_MIN)) == true &*&
        set_equals(lgn_filterowner(updateOwner(gnodes, node, INT_MIN), owner), set_remove(lgn_filterowner(gnodes, owner), gnode(node, next, value, owner))) == true;
{
    switch(gnodes) {
        case nil:
        case cons(gn, gnodes2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            lsg_gnodes_wfmap(from, 0, gnodes);
            open lsg(from, 0, gnodes);
            if(gnnode == node) {
                wfmap_contains_equal(gnodes, gnode_node, gnode(node, next, value, owner), gn);
                assert gnnext == next &*& gnvalue == value &*& gnowner == owner;
                open linkex(node, mutex, next, value, owner, nextmutex, nextvalue);
                close linkex2(node, mutex, next, value, owner);
                open unknownnode(node, next, value, owner);
                unlock_lockednode(node, next, value);
                close unknownnode(node, next, value, INT_MIN);
                updateOwner_invariant(gnodes2, node, INT_MIN);
                set_add_assoc(lgn_owners(gnodes2), INT_MIN, owner);
                set_equals_refl(lgn_filterowner(updateOwner(gnodes, node, INT_MIN), owner));
                assert !lgn_contains_node(gnodes2, node);
                assert lgn_filterowner(updateOwner(gnodes, node, INT_MIN), owner) == lgn_filterowner(gnodes2, owner);
                assert lgn_filterowner(gnodes, owner) == set_add(lgn_filterowner(gnodes2, owner), gn);
                wfmap_contains_contains_key(gnodes2, gnode_node, gn);
                assert !mem(gn, gnodes2);
                lgn_filterowner_spec(gnodes2, gn, owner);
                set_remove_not_mem(lgn_filterowner(gnodes2, owner), gn);
                assert set_remove(lgn_filterowner(gnodes2, owner), gn) == lgn_filterowner(gnodes2, owner);
                assert lgn_filterowner(updateOwner(gnodes, node, INT_MIN), owner) == set_remove(lgn_filterowner(gnodes, owner), gnode(node, next, value, owner));
                assert set_equals(lgn_filterowner(updateOwner(gnodes, node, INT_MIN), owner), set_remove(lgn_filterowner(gnodes, owner), gnode(node, next, value, owner))) == true;
                
            } else {
                lsg_gap1_helper(gnnext, gnodes2, node, next, value, owner);
                //assert false;
                assert set_subset(lgn_owners(updateOwner(gnodes2, node, INT_MIN)), set_add(lgn_owners(gnodes2), INT_MIN)) == true;
                //assert set_equals(set_add(set_add(lgn_owners(gnodes2), owner), gnowner), set_add(set_add(lgn_owners(gnodes2), gnowner), owner)) == true;
                assert lgn_owners(updateOwner(gnodes, node, INT_MIN)) == set_add(lgn_owners(updateOwner(gnodes2, node, INT_MIN)), (gnnode == node ? INT_MIN : gnowner));
                assert lgn_owners(gnodes) == set_add(lgn_owners(gnodes2), gnowner);
                                
                assert mem(gnowner, set_add(set_add(lgn_owners(gnodes2), gnowner), INT_MIN)) == true;
                assert mem(INT_MIN, set_add(set_add(lgn_owners(gnodes2), gnowner), INT_MIN)) == true;
                set_subset_set_add(lgn_owners(updateOwner(gnodes2, node, INT_MIN)), gnowner, set_add(lgn_owners(gnodes2), INT_MIN));
                assert set_subset(lgn_owners(updateOwner(gnodes2, node, INT_MIN)), set_add(set_add(lgn_owners(gnodes2), INT_MIN), gnowner)) == true;
                set_add_assoc(lgn_owners(gnodes2), INT_MIN, gnowner);
                assert set_equals(set_add(set_add(lgn_owners(gnodes2), gnowner), INT_MIN), set_add(set_add(lgn_owners(gnodes2), INT_MIN), gnowner)) == true;
                set_subset_equals_r(lgn_owners(updateOwner(gnodes2, node, INT_MIN)), set_add(set_add(lgn_owners(gnodes2), INT_MIN), gnowner), set_add(set_add(lgn_owners(gnodes2), gnowner), INT_MIN));
                assert set_subset(lgn_owners(updateOwner(gnodes2, node, INT_MIN)), set_add(set_add(lgn_owners(gnodes2), gnowner), INT_MIN)) == true;
                assert set_subset(lgn_owners(updateOwner(gnodes, node, INT_MIN)), set_add(lgn_owners(gnodes), INT_MIN)) == true;
                
                if(owner == gnowner) { 
                    assert set_equals(lgn_filterowner(updateOwner(gnodes2, node, INT_MIN), owner), set_remove(lgn_filterowner(gnodes2, owner), gnode(node, next, value, owner))) == true;
                    set_equals_add_both(lgn_filterowner(updateOwner(gnodes2, node, INT_MIN), owner), set_remove(lgn_filterowner(gnodes2, owner), gnode(node, next, value, owner)), gn);
                    assert set_equals(set_add(lgn_filterowner(updateOwner(gnodes2, node, INT_MIN), owner), gn), set_add(set_remove(lgn_filterowner(gnodes2, owner), gnode(node, next, value, owner)), gn)) == true;
                
                }
                assert set_equals(lgn_filterowner(updateOwner(gnodes, node, INT_MIN), owner), set_remove(lgn_filterowner(gnodes, owner), gnode(node, next, value, owner))) == true;
            }
            close lsg(from, 0, updateOwner(gnodes, node, INT_MIN));
            lsg_gnodes_wfmap(from, 0, updateOwner(gnodes, node, INT_MIN));
            
        }
    }
}
lemma void lsg_contains(struct llnode* from, list<gnode> gnodes, list<int> values, struct llnode* p, int pv, int value)
    requires lsg(from, 0, gnodes) &*& lgn_values(gnodes) == cons(INT_MIN, snoc(values, INT_MAX)) &*& sorted(lgn_values(gnodes)) == true &*& 
        linkex(p, ?pm, ?c, pv, ?o, ?cm, ?cv) &*& mem(gnode(p, c, pv, value), gnodes) == true &*& pv < value &*& value <= cv &*& INT_MIN < value &*& value < INT_MAX;
    ensures lsg(from, 0, gnodes) &*& linkex(p, pm, c, pv, o, cm, cv) &*& mem(value, values) == (value == cv);
{
    close lgn_contains(gnodes, p, c, pv, value);
    lsg_split(from, gnodes, p);
    assert lsg(from, p, ?gns1) &*& unknownnode(p, c, pv, value) &*& lsg(c, 0, ?gns2);
    open linkex(p, pm, c, pv, o, cm, cv);
    open link_internal(p, pm, c, pv, o, cm, cv);
    open lsg(c, 0, gns2);
    assert c != 0;
    switch(gns2) {
        case nil:
        case cons(gn, gns3):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
                assert gnnode == c;
                open unknownnode(c, gnnext, gnvalue, gnowner);
                if(gnowner == INT_MIN) open freenode(c, gnnext, gnvalue); else open lockednode(c, gnvalue, gnowner);
                open node_internal(c, ?cm2, gnvalue, gnowner);
                close linkex(p, pm, c, pv, o, cm, cv);
                close node_internal(c, cm, cv, gnowner);
                if(gnowner == INT_MIN) close freenode(c, gnnext, cv); else close lockednode(c, cv, gnowner);
                close unknownnode(c, gnnext, cv, gnowner);
                close lsg(c, 0, gns2);
                unknownnode_notnil(p);
                close lsg(p, 0, cons(gnode(p, c, pv, value), gns2));
                lsg_append(from, p, gns1, cons(gnode(p, c, pv, value), gns2));
                assert lgn_values(gnodes) == lgn_values(append(gns1, cons(gnode(p, c, pv, value), cons(gnode(c, gnnext, cv, gnowner), gns3))));
                map_append(gnode_value, gns1, cons(gnode(p, c, pv, value), cons(gnode(c, gnnext, cv, gnowner), gns3)));
                assert lgn_values(gnodes) == append(lgn_values(gns1), cons(pv, cons(cv, lgn_values(gns3))));
                assert pv < value &*& value <= cv;
                mem_snoc(value, values, INT_MAX);
                assert mem(value, values) == mem(value, lgn_values(gnodes));
                sorted_mem_append(value, lgn_values(gns1), pv, cons(cv, lgn_values(gns3)));
                sorted_append_split(lgn_values(gns1), cons(pv, cons(cv, lgn_values(gns3))));
                if(value != cv) sorted_mem_cons(value, cv, lgn_values(gns3));
        }
    }
    
}

fixpoint list<gnode> gap2(list<gnode> gns, struct llnode* node, struct llnode* new, int value)
{
    switch(gns) {
        case nil: return nil;
        case cons(gn, gns2):
            return
            switch(gn) {
                case gnode(gnnode,gnnext,gnvalue,gnowner):
                    return (gnnode == node ? 
                        cons(gnode(node, new, gnvalue, INT_MIN), cons(gnode(new, gnnext, value, INT_MIN), gns2))
                        :
                        cons(gn, gap2(gns2, node, new, value))
                    );
            };
    }
}

fixpoint list<gnode> gap3(list<gnode> gns, struct llnode* prev)
{
    switch(gns) {
        case nil: return nil;
        case cons(gn, gns2):
            return
            switch(gn) {
                case gnode(gnnode,gnnext,gnvalue,gnowner):
                    return (gnnode == prev ?
                        cons(gnode(prev, gnode_next(head(gns2)), gnvalue, INT_MIN), tail(gns2))
                        :
                        cons(gn, gap3(gns2, prev))
                    );
            };
    }
}

lemma void lsg_gap2_helper(struct llnode *from, list<gnode> gnodes, struct llnode *p, int pvalue, struct llnode *c, int v)
    requires 
        lsg(from, 0, gnodes) &*& 
        linkex(p, ?pmutex, ?n, pvalue, v, ?nmutex, v) &*& 
        node_internal(n, nmutex, v, INT_MIN) &*& 
        linkex(n, nmutex, c, v, INT_MIN, ?cmutex, ?cvalue) &*& 
        mem(gnode(p, c, pvalue, v), gnodes) == true &*& 
        sorted(lgn_values(gnodes)) == true &*&
        pvalue < v &*& v < cvalue &*& v > INT_MIN &*& v < INT_MAX;
    ensures 
        lsg(from, 0, gap2(gnodes, p, n, v)) &*&
        mutex3_held(pmutex) &*&
        is_wfmap(gap2(gnodes, p, n, v), gnode_node)==true &*&
        lgn_values(gap2(gnodes, p, n, v)) == sorted_insert(v, lgn_values(gnodes)) &*&
        set_subset(lgn_owners(gap2(gnodes, p, n, v)), set_add(lgn_owners(gnodes), INT_MIN)) == true &*&
        set_equals(lgn_filterowner(gap2(gnodes, p, n, v), v), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
{
    switch(gnodes) {
        case nil:
        case cons(gn, gnodes2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            lsg_gnodes_wfmap(from, 0, gnodes);
            open lsg(from, 0, gnodes);
            if(gnnode == p) {
                wfmap_contains_equal(gnodes, gnode_node, gnode(p, c, pvalue, v), gn);
                assert gnnext == c &*& gnvalue == pvalue &*& gnowner == v;
                open unknownnode(p, c, pvalue, v);
                open node_internal(p, _, pvalue, v);
                open linkex(p, pmutex, n, pvalue, v, nmutex, v);
                open link_internal(p, pmutex, n, pvalue, v, nmutex, v);
                open linkex(n, nmutex, c, v, INT_MIN, cmutex, cvalue);
                open link_internal(n, nmutex, c, v, INT_MIN, cmutex, cvalue);
                //assert nvalue == v;
                p->owner = INT_MIN;
                close node_internal(p, pmutex, pvalue, INT_MIN);
                close unknownnode(p, n, pvalue, INT_MIN);
                assert mutex3_held(pmutex);
                open lsg(c, 0, gnodes2);
                switch(gnodes2) {
                    case nil: assert false;
                    case cons(gn2, gnodes3):
                    switch(gn2) {
                        case gnode(gn2node, gn2next, gn2value, gn2owner):
                        assert gn2node == c;
                        open unknownnode(c, gn2next, gn2value, gn2owner);
                        open node_internal(c, _, gn2value, gn2owner);
                        close node_internal(c, cmutex, cvalue, gn2owner);
                        close unknownnode(c, gn2next, cvalue, gn2owner);
                        assert gn2value == cvalue;
                        close link(n, c, v, INT_MIN);
                        close freenode(n, c, v);
                        close unknownnode(n, c, v, INT_MIN);
                        close lsg(c, 0, gnodes2);
                        close lsg(n, 0, cons(gnode(n, c, v, INT_MIN), gnodes2));
                                                
                        set_subset_refl(lgn_owners(gnodes2));
                        set_subset_set_add(lgn_owners(gnodes2), v, lgn_owners(gnodes2));
                        set_subset_set_add(lgn_owners(gnodes2), INT_MIN, cons(v, lgn_owners(gnodes2)));
                        assert set_subset(lgn_owners(gap2(gnodes, p, n, v)), set_add(lgn_owners(gnodes), INT_MIN)) == true;
                        
                        assert lgn_filterowner(gap2(gnodes, p, n, v), v) == lgn_filterowner(gnodes2, v);
                        assert lgn_filterowner(gnodes, v) == cons(gnode(p, c, pvalue, v), lgn_filterowner(gnodes2, v));
                        wfmap_contains_contains_key(gnodes2, gnode_node, gn);
                        assert !mem(gn, gnodes2);
                        lgn_filterowner_spec(gnodes2, gn, v);
                        assert !mem(gn, lgn_filterowner(gnodes2, v));
                        set_remove_not_mem(lgn_filterowner(gnodes2, v), gn);
                        assert set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)) == lgn_filterowner(gnodes2, v);
                        set_equals_refl(lgn_filterowner(gnodes2, v));
                        assert set_equals(lgn_filterowner(gap2(gnodes, p, n, v), v), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
                    }
                } 
            } else {
                sorted_cons(gnvalue, lgn_values(gnodes2));
                lsg_gap2_helper(gnnext, gnodes2, p, pvalue, c, v);
                if(v <= gnvalue) { 
                    
                    assert pvalue < v;
                    assert v < cvalue;
                    assert mem(gnode(p, c, pvalue, v), gnodes2) == true;
                    list_split(gnodes2, gnode(p, c, pvalue, v));
                    open gres2(?gnodes2a, ?gnodes2b);
                    map_append(gnode_value, gnodes2a, cons(gnode(p, c, pvalue, v), gnodes2b));
                    assert lgn_values(gnodes2) == append(lgn_values(gnodes2a), cons(pvalue, lgn_values(gnodes2b)));
                    mem_append(pvalue, lgn_values(gnodes2a), cons(pvalue, lgn_values(gnodes2b)));
                    assert mem(pvalue, lgn_values(gnodes2)) == true;
                    sorted_mem_cons(pvalue, gnvalue, lgn_values(gnodes2));
                    assert false; 
                }
                
                assert set_subset(lgn_owners(gap2(gnodes2, p, n, v)), set_add(lgn_owners(gnodes2), INT_MIN)) == true;
                assert gap2(gnodes, p, n, v) == cons(gn, gap2(gnodes2, p, n, v));
                set_subset_set_add(lgn_owners(gap2(gnodes2, p, n, v)), gnowner, set_add(lgn_owners(gnodes2), INT_MIN));
                set_add_assoc(lgn_owners(gnodes2), gnowner, INT_MIN);
                assert set_equals(cons(INT_MIN, cons(gnowner, lgn_owners(gnodes2))), cons(gnowner, cons(INT_MIN, lgn_owners(gnodes2)))) == true;
                set_subset_equals_r(lgn_owners(gap2(gnodes2, p, n, v)), cons(gnowner, cons(INT_MIN, lgn_owners(gnodes2))), cons(INT_MIN, cons(gnowner, lgn_owners(gnodes2))));
                assert set_subset(lgn_owners(gap2(gnodes2, p, n, v)), set_add(cons(gnowner, lgn_owners(gnodes2)), INT_MIN)) == true;
                assert set_subset(cons(gnowner, lgn_owners(gap2(gnodes2, p, n, v))), set_add(cons(gnowner, lgn_owners(gnodes2)), INT_MIN)) == true;
                assert set_subset(lgn_owners(gap2(gnodes, p, n, v)), set_add(lgn_owners(gnodes), INT_MIN)) == true;
                
                assert set_equals(lgn_filterowner(gap2(gnodes2, p, n, v), v), set_remove(lgn_filterowner(gnodes2, v), gnode(p, c, pvalue, v))) == true;
                if(gnowner == v) {
                    assert lgn_filterowner(gap2(gnodes, p, n, v), v) == cons(gn, lgn_filterowner(gap2(gnodes2, p, n, v), v));
                    assert lgn_filterowner(gnodes, v) == cons(gn, lgn_filterowner(gnodes2, v));
                    assert set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)) == cons(gn, set_remove(lgn_filterowner(gnodes2, v), gnode(p, c, pvalue, v)));
                    
                    set_equals_add_both(lgn_filterowner(gap2(gnodes2, p, n, v), v), set_remove(lgn_filterowner(gnodes2, v), gnode(p, c, pvalue, v)), gn);
                    assert set_equals(lgn_filterowner(gap2(gnodes, p, n, v), v), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
                }
                assert set_equals(lgn_filterowner(gap2(gnodes, p, n, v), v), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
                
                //assert false;
            }
            close lsg(from, 0, gap2(gnodes, p, n, v));
            lsg_gnodes_wfmap(from, 0, gap2(gnodes, p, n, v));
            
        }
    }    
}



lemma void lsg_gap3_helper(struct llnode *from, list<gnode> gnodes, struct llnode *p, int pvalue, struct llnode *c, int v)
    requires lsg(from, 0, gnodes) &*&
        linkex(p, ?pmutex, ?n, pvalue, v, ?nmutex, ?nvalue) &*& 
        mem(gnode(p, c, pvalue, v), gnodes) == true &*& 
        mem(gnode(c, n, v, v), gnodes) == true &*&
        sorted(lgn_values(gnodes)) == true &*& 
        pvalue < v &*& v > INT_MIN &*& v < INT_MAX;
    ensures lsg(from, 0, gap3(gnodes, p)) &*& mutex3_held(pmutex) &*& lockednode(c, v, v) &*&
        is_wfmap(gap3(gnodes, p), gnode_node)==true &*&
        lgn_values(gap3(gnodes, p)) == remove(v, lgn_values(gnodes)) &*&
        set_subset(lgn_owners(gap3(gnodes, p)), set_add(lgn_owners(gnodes), INT_MIN)) == true &*&
        set_equals(lgn_filterowner(gap3(gnodes, p), v), set_remove(set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)), gnode(c, n, v, v))) == true;
{
    switch(gnodes) {
        case nil:
        case cons(gn, gnodes2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            lsg_gnodes_wfmap(from, 0, gnodes);
            open lsg(from, 0, gnodes);
            if(gnnode == p) {
                wfmap_contains_equal(gnodes, gnode_node, gnode(p, c, pvalue, v), gn);
                assert gnnext == c &*& gnvalue == pvalue &*& gnowner == v;
                if(p == c) {
                    open lsg(from, 0, gnodes2);
                }
                assert p != c;
                switch(gnodes2) {
                    case nil: assert false;
                    case cons(gn2, gnodes3):
                    switch(gn2) {
                        case gnode(gn2node, gn2next, gn2value, gn2owner):
                        open lsg(c, 0, gnodes2);
                        wfmap_contains_equal(gnodes2, gnode_node, gnode(c, n, v, v), gn2);
                        assert gn2node == c &*& gn2next == n &*& gn2value == v &*& gn2owner == v;
                        open linkex(p, pmutex, n, pvalue, v, nmutex, nvalue);
                        open unknownnode(p, c, pvalue, v);
                        open lockednode(p, pvalue, v);
                        open node_internal(p, _, pvalue, v);
                        p->owner = INT_MIN;
                        close node_internal(p, pmutex, pvalue, INT_MIN);
                        close link(p, n, pvalue, INT_MIN);
                        close freenode(p, n, pvalue);
                        close unknownnode(p, n, pvalue, INT_MIN);
                        close lsg(p, 0, gap3(gnodes, p));
                        open unknownnode(c, n, v, v);
                        assert lgn_owners(gap3(gnodes, p)) == cons(INT_MIN, lgn_owners(gnodes3));
                        assert lgn_owners(gnodes) == cons(v, cons(v, lgn_owners(gnodes3)));
                        set_subset_refl(lgn_owners(gnodes3));
                        set_subset_set_add(lgn_owners(gnodes3), v, lgn_owners(gnodes3));
                        set_subset_set_add(lgn_owners(gnodes3), v, cons(v, lgn_owners(gnodes3)));
                        set_subset_set_add(lgn_owners(gnodes3), INT_MIN, cons(v, cons(v, lgn_owners(gnodes3))));
                        assert set_subset(cons(INT_MIN, lgn_owners(gnodes3)), cons(INT_MIN, (cons(v, cons(v, lgn_owners(gnodes3)))))) == true;
                        assert lgn_filterowner(gap3(gnodes, p), v) == lgn_filterowner(gnodes3, v);
                        assert lgn_filterowner(gnodes, v) == cons(gnode(p, c, pvalue, v), cons(gnode(c, n, v, v), lgn_filterowner(gnodes3, v)));
                        assert !wfmap_contains_key(gnodes3, gnode_node, p);
                        wfmap_contains_contains_key(gnodes3, gnode_node, gnode(p, c, pvalue, v));
                        wfmap_contains_contains_key(gnodes3, gnode_node, gnode(c, n, v, v));

                        assert !mem(gnode(p, c, pvalue, v), gnodes3);
                        lgn_filterowner_spec(gnodes3, gnode(p, c, pvalue, v), v);
                        lgn_filterowner_spec(gnodes3, gnode(c, n, v, v), v);
                        assert !mem(gnode(p, c, pvalue, v), lgn_filterowner(gnodes3,v));
                        assert !mem(gnode(c, n, v, v), lgn_filterowner(gnodes3,v));
                        set_remove_not_mem(lgn_filterowner(gnodes3, v), gnode(p, c, pvalue, v));
                        set_remove_not_mem(lgn_filterowner(gnodes3, v), gnode(c, n, v, v));
                        assert set_remove(lgn_filterowner(gnodes, v), gnode(p,c,pvalue,v)) == cons(gnode(c, n, v, v), lgn_filterowner(gnodes3, v));
                        assert set_remove(lgn_filterowner(gnodes, v), gnode(p,c,pvalue,v)) == cons(gnode(c, n, v, v), lgn_filterowner(gnodes3, v));
                        set_equals_refl(lgn_filterowner(gnodes3, v));
                    }
                }
                assert set_subset(lgn_owners(gap3(gnodes, p)), set_add(lgn_owners(gnodes), INT_MIN)) == true;
                assert set_equals(lgn_filterowner(gap3(gnodes, p), v), set_remove(set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)), gnode(c, n, v, v))) == true;
            } else {
                if(gnnode == c) {
                    assert !wfmap_contains_key(gnodes2, gnode_node, c);
                    assert c != 0;
                    lsg_contains_next(gnnext, gnodes2, p, c, pvalue, v);
                    assert false;
                } 
                assert gnnode != c;
                assert lgn_values(gnodes) == cons(gnvalue, lgn_values(gnodes2));
                list_split(gnodes2, gnode(p, c, pvalue, v));
                open gres2(?gns2a, ?gns2b);
                assert gnodes2 == append(gns2a, cons(gnode(p, c, pvalue, v), gns2b));
                map_append(gnode_value, gns2a, cons(gnode(p, c, pvalue, v), gns2b));
                assert lgn_values(gnodes2) == append(lgn_values(gns2a), cons(pvalue, lgn_values(gns2b)));
                assert sorted(lgn_values(gnodes)) == true;
                sorted_append(gnvalue, lgn_values(gns2a), pvalue, lgn_values(gns2b));
                assert gnvalue < pvalue;
                sorted_cons(gnvalue, lgn_values(gnodes2));
                lsg_gap3_helper(gnnext, gnodes2, p, pvalue, c, v);
                close lsg(from, 0, gap3(gnodes, p));
                lsg_gnodes_wfmap(from, 0, gap3(gnodes, p));
                
                assert set_subset(lgn_owners(gap3(gnodes2, p)), set_add(lgn_owners(gnodes2), INT_MIN)) == true;
                assert gap3(gnodes, p) == cons(gn, gap3(gnodes2, p));
                assert lgn_owners(gnodes) == cons(gnowner, lgn_owners(gnodes2));
                assert lgn_owners(gap3(gnodes, p)) == cons(gnowner, lgn_owners(gap3(gnodes2, p)));
                set_subset_set_add(lgn_owners(gap3(gnodes2, p)), gnowner, set_add(lgn_owners(gnodes2), INT_MIN));
                assert set_subset(lgn_owners(gap3(gnodes2, p)), set_add(set_add(lgn_owners(gnodes2), INT_MIN), gnowner)) == true;
                set_add_assoc(lgn_owners(gnodes2), INT_MIN, gnowner);
                set_subset_equals_r(lgn_owners(gap3(gnodes2, p)), set_add(set_add(lgn_owners(gnodes2), INT_MIN), gnowner), set_add(set_add(lgn_owners(gnodes2), gnowner), INT_MIN));
                assert set_subset(cons(gnowner, lgn_owners(gap3(gnodes2, p))), set_add(cons(gnowner, lgn_owners(gnodes2)), INT_MIN)) == true;
                assert set_subset(lgn_owners(gap3(gnodes, p)), set_add(lgn_owners(gnodes), INT_MIN)) == true;
                
                if(gnowner == v) {
                    set_equals_add_both(lgn_filterowner(gap3(gnodes2, p), v), set_remove(set_remove(lgn_filterowner(gnodes2, v), gnode(p, c, pvalue, v)), gnode(c, n, v, v)), gn);
                }
                assert set_equals(lgn_filterowner(gap3(gnodes, p), v), set_remove(set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)), gnode(c, n, v, v))) == true;
            }
        }
    }
}

lemma void newres_maintains_ownedOk(list<gnode> gnodes, list<int> reserved, int v)
    requires ownedOk(gnodes, reserved) == true;
    ensures ownedOk(gnodes, snoc(reserved, v)) == true;
{
    assert set_subset(lgn_owners(gnodes), set_add(reserved, INT_MIN)) == true;
    set_subset_set_add(lgn_owners(gnodes), v, cons(INT_MIN, reserved));
    assert set_subset(lgn_owners(gnodes), set_add(set_add(reserved, INT_MIN), v)) == true;    
    set_add_assoc(reserved, v, INT_MIN);
    assert set_equals(set_add(set_add(reserved, v), INT_MIN), set_add(set_add(reserved, INT_MIN), v)) == true;
    set_equals_cons_snoc(reserved, v);
    assert set_equals(cons(v, reserved), snoc(reserved, v)) == true;
    set_equals_add_both(set_add(reserved, v), snoc(reserved, v), INT_MIN);
    assert set_equals(set_add(set_add(reserved, v), INT_MIN), set_add(snoc(reserved, v), INT_MIN)) == true;
    set_equals_transitive(set_add(set_add(reserved, INT_MIN), v), set_add(set_add(reserved, v), INT_MIN),  set_add(snoc(reserved, v), INT_MIN));
    assert set_equals(set_add(set_add(reserved, INT_MIN), v), set_add(snoc(reserved, v), INT_MIN)) == true;
    set_subset_equals_r(lgn_owners(gnodes), set_add(set_add(reserved, INT_MIN), v), set_add(snoc(reserved, v), INT_MIN));    
}
lemma void newres_no_ownednodes(list<gnode> gnodes, list<int> reserved, int val)
    requires ownedOk(gnodes, reserved) == true &*& !mem(val, reserved) &*& val != INT_MIN;
    ensures lgn_filterowner(gnodes, val) == nil;
{
    switch(gnodes) {
        case nil:
        case cons(gn, gnodes2):
            newres_no_ownednodes(gnodes2, reserved, val);
    }
}
lemma void filterowner_nil_notmem_owners(list<gnode> gnodes, int v)
    requires lgn_filterowner(gnodes, v) == nil;
    ensures !mem(v, lgn_owners(gnodes));
{
    switch(gnodes) {
        case nil:
        case cons(gn, gnodes2):
            filterowner_nil_notmem_owners(gnodes2, v);
    }
}

lemma void set_subset_remove_r2<t>(list<t> s1, list<t> s2, t v) 
    requires !mem(v, s1) &*& set_subset(s1, s2) == true;
    ensures set_subset(s1, remove(v, s2)) == true;
{
    switch(s1) {
        case nil:
        case cons(h, t):
            assert h!=v;
            neq_mem_remove(h, v, s2);
            assert mem(h, s2) == mem(h, remove(v, s2));
            set_subset_remove_r2(t, s2, v);
    }
}

lemma void removeres_maintains_ownedOk(list<gnode> gnodes, list<int> reserved, int v)
    requires ownedOk(gnodes, reserved) == true &*& set_equals(lgn_filterowner(gnodes, v), nil) == true &*& v != INT_MIN;
    ensures ownedOk(gnodes, remove(v, reserved)) == true;
{
    set_equals_empty(lgn_filterowner(gnodes, v));
    filterowner_nil_notmem_owners(gnodes, v);
    assert !mem(v, lgn_owners(gnodes));
    assert remove(v, cons(INT_MIN, reserved)) == cons(INT_MIN, remove(v, reserved));
    assert set_remove(cons(INT_MIN, reserved), v) == cons(INT_MIN, set_remove(reserved, v));
    set_subset_remove_r2(lgn_owners(gnodes), set_add(reserved, INT_MIN), v);
}

lemma void gap2_maintains_lgn_filterowner_othervalue(list<gnode> gns, struct llnode* node, struct llnode* next, int nodevalue, struct llnode* new, int value, int othervalue)
    requires mem(gnode(node, next, nodevalue, value), gns) == true &*& is_wfmap(gns, gnode_node) == true &*& value != othervalue &*& othervalue != INT_MIN &*& value != INT_MIN;
    ensures lgn_filterowner(gap2(gns, node, new, value), othervalue) == lgn_filterowner(gns, othervalue);
{
    switch(gns) {
        case nil: 
        case cons(gn, gns2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            if(gnnode == node) {
                wfmap_contains_contains_key(gns2, gnode_node, gnode(node, next, nodevalue, value));
                assert gnnext == next &*& gnvalue == nodevalue &*& gnowner == value;
                assert gap2(gns, node, new, value) == cons(gnode(node, new, nodevalue, INT_MIN), cons(gnode(new, next, value, INT_MIN), gns2));
                assert lgn_filterowner(cons(gnode(node, new, nodevalue, INT_MIN), cons(gnode(new, next, value, INT_MIN), gns2)), othervalue) ==
                           lgn_filterowner(gns2, othervalue);
                assert lgn_filterowner(gns, othervalue) == lgn_filterowner(gns2, othervalue);
            } else {
                assert gap2(gns, node, new, value) == cons(gn, gap2(gns2, node, new, value));
                gap2_maintains_lgn_filterowner_othervalue(gns2, node, next, nodevalue, new, value, othervalue);
            }
        }
    }
}
/*lemma void wflgn_contains_previous(struct llnode* from, list<gnode> gns)
    requires is_wflgn(from, 0, gns) == true &*& mem(gnode(prev, node, pvalue, value), gns) == true &*& mem(gnode(node, next, value, value), gns) == true;
    ensures from != node;
{
    switch(gns) {
        case nil:
        case cons(gn, gns2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
                assert gnnode == from &*& from != 0;
                if(gnnode
        }
    }
}
*/

lemma void wflgn_wfmap(struct llnode* from, list<gnode> gns)
    requires is_wflgn(from, 0, gns) == true; 
    ensures is_wfmap(gns, gnode_node) == true;
{
    switch(gns) {
        case nil:
        case cons(gn, gns2):
        switch(gn) { 
            case gnode(gnnode, gnnext, gnvalue, gnowner): 
                wflgn_wfmap(gnnext, gns2);
        }
    }
}    
lemma void wflgn_contains_next(struct llnode* from, list<gnode> gns, struct llnode* node, struct llnode* next, int value, int owner)
    requires is_wflgn(from, 0, gns)==true &*& mem(gnode(node, next, value, owner), gns) == true &*& next != 0; 
    ensures wfmap_contains_key(gns, gnode_node, next) == true;
{
    switch(gns) {
        case nil:
        case cons(gn, gns2):
        switch(gn) { 
            case gnode(gnnode, gnnext, gnvalue, gnowner): 
            if(gnnode == node) {
                wflgn_wfmap(from, gns); 
                //assume(is_wfmap(gns, gnode_node) == true);
                wfmap_contains_contains_key(gns, gnode_node, gnode(node, next, value, owner));
                assert gn == gnode(node, next, value, owner);
                switch(gns2) {
                    case nil: assert false;
                    case cons(gn2, gns3):
                    switch(gn2) { 
                        case gnode(gn2node, gn2next, gn2value, gn2owner): 
                        assert gn2node == next;
                    }
                }
            } else {
                wflgn_contains_next(gnnext, gns2, node, next, value, owner);
            }
        }
    } 

}

lemma void gap3_maintains_lgn_filterowner_othervalue(struct llnode* from, list<gnode> gns, struct llnode* prev, int pvalue, struct llnode* node, struct llnode* next, int value, int othervalue)
    requires is_wflgn(from, 0, gns)==true &*& mem(gnode(prev, node, pvalue, value), gns) == true &*& mem(gnode(node, next, value, value), gns) == true &*& value != othervalue &*& othervalue != INT_MIN &*& value != INT_MIN;
    ensures lgn_filterowner(gap3(gns, prev), othervalue) == lgn_filterowner(gns, othervalue);
{
    switch(gns) {
        case nil:
        case cons(gn, gns2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
                assert gnnode != 0;
                if(gnnode == prev) {
                    assume(false);
                } else {
                    if(gnnode == node) {
                        assert !wfmap_contains_key(gns2, gnode_node, node);
                        wflgn_contains_next(gnnext, gns2, prev, node, pvalue, value);
                        assert false;
                    }
                    assert gnnode != node;
                    gap3_maintains_lgn_filterowner_othervalue(gnnext, gns2, prev, pvalue, node, next, value, othervalue);
                }
        }
    }
}

lemma void gap3_maintains_lgn_filterowner_othervalue2(list<gnode> gns, struct llnode* prev, int pvalue, struct llnode* node, struct llnode* next, int value, int othervalue)
    requires is_wflgn(gnode_node(head(gns)), 0, gns)==true &*& mem(gnode(prev, node, pvalue, value), gns) == true &*& mem(gnode(node, next, value, value), gns) == true &*& value != othervalue &*& othervalue != INT_MIN &*& value != INT_MIN;
    ensures lgn_filterowner(gap3(gns, prev), othervalue) == lgn_filterowner(gns, othervalue);
{
    switch(gns) {
        case nil:
        case cons(gn, gns2):
        switch(gn) {
            case gnode(gnnode, gnnext, gnvalue, gnowner):
            gap3_maintains_lgn_filterowner_othervalue(gnnode, gns, prev, pvalue, node, next, value, othervalue);
        }
    }
}
//TODO: make ghost field for owner;

box_class fset_box(struct fset *s, list<int> values, list<gnode> gnodes, map<int, handle> reserved) {
    invariant 
        [1/2] s->set |-> ?h &*&
        h != 0 &*&
        lsg(h, 0, gnodes) &*&
        is_wfmap(gnodes, gnode_node) == true &*& 
        is_wflgn(h, 0, gnodes) == true &*& gnode_node(head(gnodes)) == h &*&
        lgn_values(gnodes) == cons(INT_MIN, snoc(values, INT_MAX)) &*&
        sorted(lgn_values(gnodes)) == true &*&
        [1/2]s->res |-> map_keys(reserved) &*&
        ownedOk(gnodes, map_keys(reserved)) == true &*& //only reserved values can lock a node
        !map_contains_key(reserved, INT_MIN) &*&
        !map_contains_key(reserved, INT_MAX);  

    action observe();
        requires true;
        ensures values == old_values && gnodes == old_gnodes && reserved == old_reserved;
        
    action acquire_changeperm(int v);
        requires !map_contains_key(reserved, v) && INT_MIN < v && v < INT_MAX;
        ensures reserved == map_put(old_reserved, v, actionHandle) && values == old_values && gnodes == old_gnodes;

    action release_changeperm(int v); 
        requires map_contains(reserved, v, actionHandle) && set_equals(lgn_filterowner(gnodes, v), set_empty());
        ensures reserved == map_remove(old_reserved, v) && values == old_values && gnodes == old_gnodes;

    action change(struct llnode* node, int v);
        requires map_contains(reserved, v, actionHandle) && lgn_contains_freenode(gnodes, node);
        ensures gnodes == updateOwner(old_gnodes, node, v) && values == old_values && reserved == old_reserved;

    action gap1(struct llnode* node, struct llnode* next, int value, int v); // put back the link unchanged
        requires map_contains(reserved, v, actionHandle) && lgn_contains_fullnode(gnodes, node, next, value, v) == true;
        ensures gnodes == updateOwner(old_gnodes, node, INT_MIN) && values == old_values && reserved == old_reserved ;
            
    action gap2(struct llnode* node, struct llnode* next, int value, int v, struct llnode* new); // insert value
        requires map_contains(reserved, v, actionHandle) && mem(gnode(node, next, value, v), gnodes) == true; //TODO: proof that v < nextvalue
        ensures gnodes == gap2(old_gnodes, node, new, v) && values == sorted_insert(v, old_values) && reserved == old_reserved;

    action gap3(struct llnode* node, struct llnode* next, int value, int v, struct llnode* nextnext); // remove value
        requires map_contains(reserved, v, actionHandle) && mem(gnode(node, next, value, v), gnodes) == true && mem(gnode(next, nextnext, v, v), gnodes) == true;
        ensures gnodes == gap3(old_gnodes, node) && values == remove(v, old_values) && reserved == old_reserved;

    handle_predicate changeperm(int val, bool m, list<gnode> owned) {
        invariant 
            val > INT_MIN && 
            val < INT_MAX &&
            map_contains(reserved, val, predicateHandle) &&
            m == mem(val, values) &&
            set_equals(owned, lgn_filterowner(gnodes, val));
            
        preserved_by observe() {
        }
        preserved_by acquire_changeperm(v) {
            map_contains_spec(old_reserved, val, predicateHandle);
            assert val!=v;
            map_put_maintains_map_contains(old_reserved, val, predicateHandle, v, actionHandle);
        }
        preserved_by release_changeperm(v) {
            map_contains_functional(old_reserved, v, actionHandle, val, predicateHandle);        
            assert val!=v;
            map_remove_maintains_map_contains(old_reserved, val, predicateHandle, v);
        }
        preserved_by change(node, v) {
            map_contains_functional(old_reserved, v, actionHandle, val, predicateHandle);        
            assert val!=v;
            assert lgn_contains_freenode(old_gnodes, node) == true;
            assert gnodes == updateOwner(old_gnodes, node, v);
            lock_freenode_otherowner(old_gnodes, node, v, val);
        }
        preserved_by gap1(node, next, value, v) {
            map_contains_functional(old_reserved, v, actionHandle, val, predicateHandle);
            assert val!=v;
            assert lgn_contains_fullnode(old_gnodes, node, next, value, v) == true;
            map_contains_spec(old_reserved, v, actionHandle);
            free_lockednode_otherowner(old_gnodes, node, next, value, v, val);
        }
        preserved_by gap2(node, next, value, v, new) {
            map_contains_functional(old_reserved, v, actionHandle, val, predicateHandle);
            assert val!=v;
            assert lgn_contains_fullnode(old_gnodes, node, next, value, v) == true;
            sorted_cons(INT_MIN, append(old_values, cons(INT_MAX, nil)));
            sorted_append_split2(old_values, cons(INT_MAX, nil));
            sorted_insert_mem_increasing(old_values, v, val);
            map_contains_spec(old_reserved, v, actionHandle);
            gap2_maintains_lgn_filterowner_othervalue(old_gnodes, node, next, value, new, v, val);
            assert gnodes == gap2(old_gnodes, node, new, v);
        }
        preserved_by gap3(node,next,value,v,nextnext)
        {
            map_contains_functional(old_reserved, v, actionHandle, val, predicateHandle);
            assert val!=v;
            assert lgn_contains_fullnode(old_gnodes, node, next, value, v) == true;
            assert lgn_contains_fullnode(old_gnodes, next, nextnext, v, v) == true;
            sorted_cons(INT_MIN, snoc(old_values, INT_MAX));
            sorted_snoc(old_values, INT_MAX);
            sorted_remove_all2(v, old_values);
            assert values == remove_all2(v, old_values);
            remove_all2_spec(v, val, old_values);
            assert m == mem(val, values);
            map_contains_spec(old_reserved, v, actionHandle);
            gap3_maintains_lgn_filterowner_othervalue2(old_gnodes, node, value, next, nextnext, v, val);
            
        }
    }
}

lemma void changeperm_disjoint(handle h1, handle h2) //TODO: this should hold, right?
    requires changeperm(h1, ?boxId, ?v, ?b, ?mg1) &*& changeperm(h2, boxId, ?v2, ?b2, ?mg2);
    ensures changeperm(h1, boxId, v, b, mg1) &*& changeperm(h2, boxId, v2, b2, mg2) &*& h1 != h2;
{
    assume (false);
}

predicate_ctor fbm_inv(struct fset* f, box boxId) () = 
    fset_box(boxId, f, ?values, ?gnodes, ?reserved);

predicate fset_internal(struct fset* f; box boxId) = 
    malloc_block_fset(f) &*&
    f != 0 &*&
    f->boxMutex |-> ?boxMutex &*&
    f->boxId |-> boxId &*&
    [1/2] f->set |-> ?s &*&
    s != 0 &*&
    [1/3] s->mutex |-> ?mutex &*&
    mutex3(mutex) &*&
    [1/3] s->value |-> INT_MIN &*&
    mutex(boxMutex, fbm_inv(f, boxId));

predicate fset_internal_ex(struct fset* f; box boxId, struct llnode* shead, struct mutex3* sheadmutex) = 
    malloc_block_fset(f) &*&
    f != 0 &*&
    f->boxMutex |-> ?boxMutex &*&
    f->boxId |-> boxId &*&
    mutex(boxMutex, fbm_inv(f, boxId)) &*&
    [1/2] f->set |-> shead &*&
    shead != 0 &*&
    [1/3] shead->value |-> INT_MIN &*&
    [1/3] shead->mutex |-> sheadmutex &*&
    mutex3(sheadmutex);
    
predicate fset(struct fset* s, list<int> res) =
    counting(fset_internal, s, 1+length(res), ?boxId) &*&
    ticket(fset_internal, s, ?f) &*&
    [f] fset_internal(s, boxId) &*&
    [1/2] s->res |-> res;

predicate own(struct fset* s, int v, bool b) = 
    ticket(fset_internal, s, ?f) &*&
    [f] fset_internal(s, ?boxId) &*& 
    changeperm(?h, boxId, v, b, nil);


@*/


void own_disjoint(struct fset* s, int v)
    //@ requires own(s, v, ?b) &*& own(s, v, ?b2);
    //@ ensures false;
{
    //@ open own(s, v, b); 
    //@ assert changeperm(?h1, ?boxId, v, b, ?mg1);
    //@ open own(s, v, b2);
    //@ assert changeperm(?h2, boxId, v, b2, ?mg2);
    //@ changeperm_disjoint(h1, h2);
    //@ assert (h1 != h2);
    
    //@ open [?f]fset_internal(s, boxId);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate changeperm(h1, v, b, mg1)
        perform_action observe() {
    @*/
    {
    }
    /*@
        }
        producing_box_predicate fset_box(s, values, gnodes, reserved)
        producing_handle_predicate changeperm(v, b, mg1);
    @*/

    /*@ consuming_box_predicate fset_box(boxId, s, ?values2, ?gnodes2, ?reserved2)
        consuming_handle_predicate changeperm(h2, v, b2, mg2)
        perform_action observe() {
    @*/
    {
    }
    /*@
        }
        producing_box_predicate fset_box(s, values2, gnodes2, reserved2)
        producing_handle_predicate changeperm(v, b2, mg2);
    @*/
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);

    //@ map_contains_functional(reserved, v, h1, v, h2);
}

 
void acquire_own(struct fset* s, int v)
    //@ requires fset(s, ?vs) &*& !mem(v, vs) &*& v > INT_MIN &*& v < INT_MAX;
    //@ ensures fset(s, snoc(vs, v)) &*& own(s, v, ?b);
{
    //@ open fset(s, vs);
    //@ open [?f]fset_internal(s, ?boxId);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    
    //@ handle h = create_handle fset_box_handle(boxId);
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate fset_box_handle(h)
        perform_action acquire_changeperm(v) {
    @*/
    {
        //@ map_contains_key_mem_map_keys(reserved, v);
        //@ s->res = snoc(vs, v); 
        //@ map_put_map_keys(reserved, v, h);
        //@ map_put_causes_map_contains(reserved, v, h);
        //@ assert map_keys(map_put(reserved, v, h)) == snoc(map_keys(reserved), v);
        //@ newres_maintains_ownedOk(gnodes, map_keys(reserved), v);
        //@ newres_no_ownednodes(gnodes, map_keys(reserved), v);
        //@ map_contains_key_after_put(reserved, INT_MIN, v, h); 
        //@ map_contains_key_after_put(reserved, INT_MAX, v, h); 
    }
    /*@
        }
        producing_box_predicate fset_box(s, values, gnodes, map_put(reserved, v, h))
        producing_handle_predicate changeperm(v, mem(v, values), nil);
    @*/
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);
    //@ create_ticket(fset_internal, s);
    //@ close own(s, v, mem(v, values));
    //@ close [f] fset_internal(s, boxId);
    //@ close fset(s, snoc(vs, v)); 
}



void release_own(struct fset* s, int v)
    //@ requires fset(s, ?vs) &*& own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ ensures fset(s, remove(v, vs));
{
    //@ open fset(s, vs);
    //@ open [?f]fset_internal(s, ?boxId);
    //@ open own(s, v, b);
    //@ destroy_ticket(fset_internal, s);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
        
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate changeperm(?h, v, b, nil)
        perform_action release_changeperm(v) {
    @*/
    {
        //@ map_contains_spec(reserved, v, h);
        //@ map_contains_key_mem_map_keys(reserved, v);
        //@ s->res = remove(v, vs);
        //@ map_remove_map_keys(reserved, v);
        //@ removeres_maintains_ownedOk(gnodes, map_keys(reserved), v);
        //@ map_contains_key_after_remove(reserved, INT_MIN, v); 
        //@ map_contains_key_after_remove(reserved, INT_MAX, v); 
    }
    /*@
        }
        producing_box_predicate fset_box(s, values, gnodes, map_remove(reserved, v))
        producing_handle_predicate fset_box_handle();
    @*/
    //@ leak fset_box_handle(h, boxId);
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);

    //@ close [f] fset_internal(s, boxId);
    //@ assert vs != nil;
    //@ close fset(s, remove(v, vs)); 
}

 
struct fset* screate() 
    //@requires true;
    //@ensures fset(result, nil);
{
    struct llnode* t = malloc(sizeof(struct llnode));
    if(t == 0) abort();
    struct mutex3* m = create_mutex3();
    t->mutex = m;
    mutex3_release(m);
    t->value = INT_MAX;
    t->next = 0;
    //@ t->owner = INT_MIN;
    //@ close node_internal(t, m, INT_MAX, INT_MIN);
    //@ close freenode(t, 0, INT_MAX);
    //@ close unknownnode(t, 0, INT_MAX, INT_MIN);
    //@ close lsg(0, 0, nil);
    //@ close lsg(t, 0, cons(gnode(t,0,INT_MAX,INT_MIN), nil));
    struct llnode* h = malloc(sizeof(struct llnode));
    if(h == 0) abort();
    h->value = INT_MIN;
    h->next = t;
    m = create_mutex3();
    h->mutex = m;
    mutex3_release(m);
    //@ h->owner = INT_MIN;
    //@ close node_internal(h, m, INT_MIN, INT_MIN);
    //@ close freenode(h, t, INT_MIN);
    //@ close unknownnode(h, t, INT_MIN, INT_MIN);
    //@ close lsg(h, 0, cons(gnode(h,t,INT_MIN,INT_MIN), cons(gnode(t,0,INT_MAX,INT_MIN), nil)));
    struct fset* s = malloc(sizeof(struct fset));
    if(s == 0) abort();
    s->set = h;
    //@ s->res = nil;
    //@ create_box boxId = fset_box(s, nil, cons(gnode(h,t,INT_MIN,INT_MIN), cons(gnode(t,0,INT_MAX,INT_MIN), nil)) , mnil);
    //@ s->boxId = boxId;
    //@ close fbm_inv(s, boxId)();
    //@ close create_mutex_ghost_arg(fbm_inv(s, boxId));
    struct mutex* boxMutex = create_mutex();
    s->boxMutex = boxMutex;
    //@ close fset_internal(s, boxId);
    //@ start_counting(fset_internal, s);
    //@ create_ticket(fset_internal, s);
    //@ close fset(s, nil);
    return s;
}
/*@
@*/
void sdispose(struct fset* s) 
    //@requires fset(s, nil); 
    //@ensures true;
{
    //@ open fset(s, nil);
    //@ destroy_ticket(fset_internal, s);
    //@ stop_counting(fset_internal, s);
    //@ open fset_internal(s, ?boxId);
    mutex_dispose(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    //@ dispose_box fset_box(boxId, s, ?values, ?gnodes, ?reserved);
    //@ assert ownedOk(gnodes, nil) == true;
    struct llnode* l = s->set;
    free(s);
    struct llnode *c = l; 
    //@ list<gnode> cur_gnodes = gnodes;
    while(c!=0) 
    //@ invariant (c == 0 ? true : [1/3]c->mutex |-> ?mutex &*& mutex3(mutex) &*& [1/3]c->value |-> ?value) &*& lsg(c, 0, cur_gnodes) &*& ownedOk(cur_gnodes, nil) == true;
    {
        //@ open lsg(c, 0, cur_gnodes);
        //@ open unknownnode(c, ?cn, ?cv, ?co);
        //@ open freenode(c, cn, cv);
        //@  open node_internal(c, _, cv, co);
        struct llnode* n = c->next;
        mutex3_acquire(c->mutex);
        mutex3_dispose(c->mutex);
        free(c);
        c = n;
        //@ cur_gnodes = tail(cur_gnodes);
    }
    //@ open lsg(c, 0, _);
}

void perform_change_head(struct fset* s, int v) 
/*@ requires [?f]fset_internal_ex(s, ?boxId, ?sh, ?shmutex) &*& changeperm(?h, boxId, v, ?b, ?owned) &*& mutex3_held(shmutex) &*& v > INT_MIN &*& v < INT_MAX;
@*/
/*@
    ensures [f]fset_internal_ex(s, boxId, sh, shmutex) &*& linkex(sh, shmutex, ?shnext, INT_MIN, v, _, _) &*& changeperm(h, boxId, v, b, set_add(owned, gnode(sh, shnext, INT_MIN, v)));
@*/
{
    //@ open [f]fset_internal_ex(s, boxId, sh, shmutex);
    struct llnode* p = s->set;
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    //@ struct llnode *pnext = 0;
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate changeperm(h, v, b, owned)
        perform_action change(p, v) {
    @*/
    {
        //@ assert map_contains(reserved, v, h) == true; //precondition 1
        //@ lsg_contains_head(p, gnodes);
        //@ last_snoc(values, INT_MAX);
        //@ lsg_locknode(p, gnodes, p, v);
        //@ assert lgn_contains_freenode(gnodes, p) == true; //precondition 2
        //@ map_contains_spec(reserved, v, h);
        //@ map_contains_key_mem_map_keys(reserved, v);
        //@ set_subset_transitive(lgn_owners(updateOwner(gnodes, p, v)), set_add(lgn_owners(gnodes), v), set_add(map_keys(reserved), INT_MIN));
        //@ assert linkex(p, shmutex, ?pn, INT_MIN, v, ?pnm, ?pnv);
        //@ pnext = pn;        
        //@ set_equals_add_both(owned, lgn_filterowner(gnodes, v), gnode(p, pn, INT_MIN, v));
        //@ set_equals_transitive(set_add(owned, gnode(p, pnext, INT_MIN, v)), set_add(lgn_filterowner(gnodes, v), gnode(p, pn, INT_MIN, v)), lgn_filterowner(updateOwner(gnodes, p, v), v));
        //@ lsg_gnodes_is_wflgn_helper(p);
    }
    /*@
        }
        producing_box_predicate fset_box(s, values, updateOwner(gnodes, p, v), reserved)
        producing_handle_predicate changeperm(v, b, set_add(owned, gnode(p, pnext, INT_MIN, v)));
    @*/
    //@ close fbm_inv(s, boxId)();    
    mutex_release(s->boxMutex);   
    //@ close [f]fset_internal_ex(s, boxId, sh, shmutex);
}

//TODO: replace contains_fullnode with mem

void perform_change_other(struct fset* s, int v, struct llnode* p, struct llnode* c) //TODO: refactor to support any owned
/*@ requires [?f]fset_internal(s, ?boxId) &*& changeperm(?h, boxId, v, ?b, ?owned) &*& 
        linkex(p, ?pmutex, c, ?pvalue, v, ?cmutex, ?cvalue) &*& mutex3_held(cmutex) &*&
        mem(gnode(p, c, pvalue, v), owned) == true &*&
        cvalue < INT_MAX &*& 
        v > INT_MIN &*& 
        v < INT_MAX;
@*/
/*@
    ensures                 
        [f]fset_internal(s, boxId) &*&
        linkex(p, pmutex, c, pvalue, v, cmutex, cvalue) &*& 
        linkex(c, cmutex, ?cnext, cvalue, v, _, _) &*&
        changeperm(h, boxId, v, b, set_add(owned, gnode(c, cnext, cvalue, v)));
@*/
{
    //@ open [f]fset_internal(s, boxId);
    //@ open linkex(p, pmutex, c, pvalue, v, cmutex, cvalue);
    //@ open link_internal(p, pmutex, c, pvalue, v, cmutex, cvalue);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    //@ struct llnode* cnext=0;
    /*@ consuming_box_predicate fset_box(boxId, s, ?values2, ?gnodes2, ?reserved2)
        consuming_handle_predicate changeperm(h, v, b, owned)
        perform_action change(c, v) {
    @*/
    {
        //@ assert [_]s->set |-> ?head;
        //@ assert map_contains(reserved2, v, h) == true; //precondition 1
        //@ lgn_filterowner_spec(gnodes2, gnode(p, c, pvalue, v), v);
        //@ set_equals_mem(owned, lgn_filterowner(gnodes2, v), gnode(p, c, pvalue, v));
        //@ lsg_contains_next(head, gnodes2, p, c, pvalue, v);
        //@ last_snoc(values2, INT_MAX);
        //@ lsg_locknode(head, gnodes2, c, v);
        //@ assert lgn_contains_freenode(gnodes2, c) == true; //precondition 2
        //@ map_contains_spec(reserved2, v, h);
        //@ map_contains_key_mem_map_keys(reserved2, v);
        //@ set_subset_transitive(lgn_owners(updateOwner(gnodes2, c, v)), set_add(lgn_owners(gnodes2), v), set_add(map_keys(reserved2), INT_MIN));
        //@ assert linkex(c, cmutex, ?cn, cvalue, v, ?cnm, ?cnv);
        //@ cnext = cn;        
        //@ set_equals_add_both(owned, lgn_filterowner(gnodes2, v), gnode(c, cn, cvalue, v));
        // @ assert set_equals(lgn_filterowner(updateOwner(gnodes2, c, v), v), ) == true;
        //@ set_equals_transitive(set_add(owned, gnode(c, cnext, cvalue, v)), set_add(lgn_filterowner(gnodes2, v), gnode(c, cn, cvalue, v)), lgn_filterowner(updateOwner(gnodes2, c, v), v));
        //@ assert set_equals(set_add(owned, gnode(c, cnext, cvalue, v)), lgn_filterowner(updateOwner(gnodes2, c, v), v)) == true;
        //@ lsg_gnodes_is_wflgn_helper(head);
    }
    /*@
        }
        producing_box_predicate fset_box(s, values2, updateOwner(gnodes2, c, v), reserved2)
        producing_handle_predicate changeperm(v, b, set_add(owned, gnode(c, cnext, cvalue, v)));
    @*/
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);
    //@ close [f]fset_internal(s, boxId);
        
    //@ close linkex(p, pmutex, c, pvalue, v, cmutex, cvalue);
}

void perform_gap1(struct fset* s, int v, struct llnode* p) 
/*@ requires [?f]fset_internal(s, ?boxId) &*& changeperm(?h, boxId, v, ?b, ?owned) &*& 
        linkex(p, ?pmutex, ?c, ?pvalue, v, ?cmutex, ?cvalue) &*& mem(gnode(p, c, pvalue, v), owned) == true &*& v > INT_MIN &*& v < INT_MAX;
@*/
/*@
    ensures [f]fset_internal(s, boxId) &*& mutex3_held(pmutex) &*& changeperm(h, boxId, v, b, set_remove(owned, gnode(p, c, pvalue, v)));
@*/
{
    //@ open [f]fset_internal(s, boxId);
    //@ open linkex(p, pmutex, c, pvalue, v, cmutex, cvalue);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate changeperm(h, v, b, owned)
        perform_action gap1(p, c, pvalue, v) {
    @*/
    {
        //@ assert [1/2] s->set |-> ?head;
        //@ assert map_contains(reserved, v, h) == true; //precondition 1
        //@ assert mem(gnode(p, c, pvalue, v), owned) == true;
        //@ set_equals_mem(owned, lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v));
        //@ lgn_filterowner_spec(gnodes, gnode(p, c, pvalue, v), v);
        //@ assert lgn_contains_fullnode(gnodes, p, c, pvalue, v) == true; //precondition 2
        //@ lsg_gap1_helper(head, gnodes, p, c, pvalue, v);
        //@ set_subset_transitive(lgn_owners(updateOwner(gnodes, p, INT_MIN)), set_add(lgn_owners(gnodes), INT_MIN), set_add(map_keys(reserved), INT_MIN));
        // set_equals(lgn_filterowner(updateOwner(gnodes, node, INT_MIN), owner), set_remove(lgn_filterowner(gnodes, owner), gnode(node, next, value, owner))) == true;
        //@ assert set_equals(owned, lgn_filterowner(gnodes, v)) == true;
        //@ assert set_equals(lgn_filterowner(updateOwner(gnodes, p, INT_MIN), v), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
        //@ set_equals_set_remove(owned, lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v));
        //@ assert set_equals(set_remove(owned, gnode(p, c, pvalue, v)), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
        //@ set_equals_transitive(set_remove(owned, gnode(p, c, pvalue, v)), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)), lgn_filterowner(updateOwner(gnodes, p, INT_MIN), v));
        //@ assert set_equals(set_remove(owned, gnode(p, c, pvalue, v)), lgn_filterowner(updateOwner(gnodes, p, INT_MIN), v)) == true;
        //@ lsg_gnodes_is_wflgn_helper(head);
    }
    /*@
        }
        producing_box_predicate fset_box(s, values, updateOwner(gnodes, p, INT_MIN), reserved)
        producing_handle_predicate changeperm(v, b, set_remove(owned, gnode(p, c, pvalue, v)));
    @*/
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);
    //@ close [f]fset_internal(s, boxId);        
}
void perform_gap2(struct fset* s, int v, struct llnode* p) 
/*@ requires [?f]fset_internal(s, ?boxId) &*& changeperm(?h, boxId, v, ?b, ?owned) &*&
        node_internal(?n, ?nmutex, v, INT_MIN) &*& linkex(p, ?pmutex, n, ?pvalue, v, nmutex, v) &*& linkex(n, nmutex, ?c, v, INT_MIN, ?cmutex, ?cvalue) &*& 
        mem(gnode(p, c, pvalue, v), owned) == true &*& pvalue < v &*& v < cvalue &*& v > INT_MIN &*& v < INT_MAX ;
@*/
/*@
    ensures [f]fset_internal(s, boxId) &*& mutex3_held(pmutex) &*& changeperm(h, boxId, v, true, set_remove(owned, gnode(p, c, pvalue, v)));
@*/
{
    //@ open [f]fset_internal(s, boxId);
    // @ open linkex(p, pmutex, c, cmutex, cvalue);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate changeperm(h, v, b, owned)
        perform_action gap2(p, c, pvalue, v, n) {
    @*/
    {
        //@ assert [1/2] s->set |-> ?shead;
        //@ assert map_contains(reserved, v, h) == true; //precondition 1
        //@ assert mem(gnode(p, c, pvalue, v), owned) == true;
        //@ set_equals_mem(owned, lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v));
        //@ lgn_filterowner_spec(gnodes, gnode(p, c, pvalue, v), v);
        //@ assert mem(gnode(p, c, pvalue, v), gnodes) == true; 
        //@ lsg_gap2_helper(shead, gnodes, p, pvalue, c, v);
        //@ si1(v, values);
        //@ sorted_insert_sorted(v, lgn_values(gnodes));
        //@ assert set_subset(lgn_owners(gap2(gnodes, p, n, v)), set_add(lgn_owners(gnodes), INT_MIN)) == true;
        //@ assert set_subset(lgn_owners(gnodes), set_add(map_keys(reserved), INT_MIN)) == true;
        //@ assert set_subset(set_add(lgn_owners(gnodes), INT_MIN), set_add(map_keys(reserved), INT_MIN)) == true;
        //@ set_subset_transitive(lgn_owners(gap2(gnodes, p, n, v)), set_add(lgn_owners(gnodes), INT_MIN), set_add(map_keys(reserved), INT_MIN));
        //@ assert ownedOk(gap2(gnodes, p, n, v), map_keys(reserved)) == true;
        //@ sorted_insert_mem(v, values);
        //@ assert mem(v, sorted_insert(v, values)) == true;
        //@ assert set_equals(lgn_filterowner(gap2(gnodes, p, n, v), v), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
        //@ assert set_equals(owned, lgn_filterowner(gnodes, v)) == true;
        //@ set_equals_set_remove(owned, lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v));
        //@ assert set_equals(set_remove(owned, gnode(p, c, pvalue, v)), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v))) == true;
        //@ set_equals_transitive(set_remove(owned, gnode(p, c, pvalue, v)), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)), lgn_filterowner(gap2(gnodes, p, n, v), v));
        //@ assert set_equals(set_remove(owned, gnode(p, c, pvalue, v)), lgn_filterowner(gap2(gnodes, p, n, v), v)) == true;
        //@ lsg_gnodes_is_wflgn_helper(shead);
    }
    /*@
        }
        producing_box_predicate fset_box(s, sorted_insert(v, values), gap2(gnodes, p, n, v), reserved)
        producing_handle_predicate changeperm(v, true, set_remove(owned, gnode(p, c, pvalue, v)));
    @*/
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);
    //@ close [f]fset_internal(s, boxId);        
}

void perform_gap3(struct fset* s, int v, struct llnode* p, struct llnode* c) 
/*@ requires [?f]fset_internal(s, ?boxId) &*& changeperm(?h, boxId, v, ?b, ?owned) &*&
        linkex(p, ?pmutex, ?n, ?pvalue, v, ?nmutex, ?nvalue) &*& 
        mem(gnode(p, c, pvalue, v), owned) == true &*& mem(gnode(c, n, v, v), owned) == true &*& pvalue < v &*&
        v > INT_MIN &*& v < INT_MAX ;
@*/
/*@
    ensures [f]fset_internal(s, boxId) &*& mutex3_held(pmutex) &*& lockednode(c, v, v) &*&
        changeperm(h, boxId, v, false, set_remove(set_remove(owned, gnode(p, c, pvalue, v)), gnode(c, n, v, v)));
@*/
{
    //@ open [f]fset_internal(s, boxId);
    // @ open linkex(p, pmutex, c, cmutex, cvalue);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate changeperm(h, v, b, owned)
        perform_action gap3(p, c, pvalue, v, n) {
    @*/
    {
        //@ assert [1/2] s->set |-> ?shead;
        //@ assert map_contains(reserved, v, h) == true; //precondition 1
        //@ set_equals_mem(owned, lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v));
        //@ lgn_filterowner_spec(gnodes, gnode(p, c, pvalue, v), v);
        //@ set_equals_mem(owned, lgn_filterowner(gnodes, v), gnode(c, n, v, v));
        //@ lgn_filterowner_spec(gnodes, gnode(c, n, v, v), v);
        //@ assert mem(gnode(p, c, pvalue, v), owned) == true;
        //@ assert mem(gnode(c, n, v, v), owned) == true;
        //@ lsg_gap3_helper(shead, gnodes, p, pvalue, c, v);
        //@ remove_helper1(v, values);
        //@ remove_sorted(v, lgn_values(gnodes));
        
        //@ set_subset_transitive(lgn_owners(gap3(gnodes, p)), set_add(lgn_owners(gnodes), INT_MIN), set_add(map_keys(reserved), INT_MIN));
        //@ assert ownedOk(gap3(gnodes, p), map_keys(reserved)) == true;
        //@ sorted_cons(INT_MIN, snoc(values, INT_MAX));
        //@ sorted_snoc(values, INT_MAX);
        //@ sorted_remove_all2(v, values);
        //@ remove_all2_mem(v, v, values);
        //@ assert !mem(v, remove(v, values));

        //@ set_equals_set_remove(owned, lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v));
        //@ set_equals_set_remove(set_remove(owned, gnode(p, c, pvalue, v)), set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)), gnode(c, n, v, v));
        /*@ set_equals_transitive(set_remove(set_remove(owned, gnode(p, c, pvalue, v)), gnode(c, n, v, v)), 
                                  set_remove(set_remove(lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v)), gnode(c, n, v, v)), 
                                  lgn_filterowner(gap3(gnodes, p), v));
        @*/
        //@ assert set_equals(lgn_filterowner(gap3(gnodes, p), v), set_remove(set_remove(owned, gnode(p, c, pvalue, v)), gnode(c, n, v, v))) == true;
        //@ lsg_gnodes_is_wflgn_helper(shead);
    }
    /*@
        }
        producing_box_predicate fset_box(s, remove(v, values), gap3(gnodes, p), reserved)
        producing_handle_predicate changeperm(v, false, set_remove(set_remove(owned, gnode(p, c, pvalue, v)), gnode(c, n, v, v)));
    @*/
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);
    //@ close [f]fset_internal(s, boxId);        
}

//TODO: perform_obs_mem can probably be integrated into change

void perform_obs_mem(struct fset* s, int v, struct llnode* p)
//@ requires [?f]fset_internal(s, ?boxId) &*& changeperm(?h, boxId, v, ?b, ?owned) &*& linkex(p, ?pm, ?c, ?pvalue, v, ?cm, ?cvalue) &*& mem(gnode(p, c, pvalue, v), owned) == true &*& pvalue < v &*& v <= cvalue;
//@ ensures [f]fset_internal(s, boxId) &*& changeperm(h, boxId, v, b, owned) &*& linkex(p, pm, c, pvalue, v, cm, cvalue) &*& b == (cvalue == v);
{
    //@ open [f]fset_internal(s, boxId);
    mutex_acquire(s->boxMutex);
    //@ open fbm_inv(s, boxId)();
    /*@ consuming_box_predicate fset_box(boxId, s, ?values, ?gnodes, ?reserved)
        consuming_handle_predicate changeperm(h, v, b, owned)
        perform_action observe() {
    @*/
    {
        //@ assert [1/2]s->set |-> ?head;
        //@ set_equals_mem(owned, lgn_filterowner(gnodes, v), gnode(p, c, pvalue, v));
        //@ lgn_filterowner_spec(gnodes, gnode(p, c, pvalue, v), v);
        //@ lsg_contains(head, gnodes, values, p, pvalue, v);
    }
    /*@
        }
        producing_box_predicate fset_box(s, values, gnodes, reserved)
        producing_handle_predicate changeperm(v, (cvalue == v), owned);
    @*/
    //@ close fbm_inv(s, boxId)();
    mutex_release(s->boxMutex);
    //@ close [f]fset_internal(s, boxId);
}

struct llnode* slocate(struct fset* s, int v) 
//@ requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX; 
/*@ ensures [?frac]fset_internal(s, ?boxId) &*& ticket(fset_internal, s, frac) &*& linkex(result, _, ?next, ?value, v, _, ?nvalue) &*&
        changeperm(?h, boxId, v, b, cons(gnode(result, next, value, v), nil)) &*& value < v &*& v <= nvalue &*& b == (v == nvalue);
@*/
{
    //@ open own(s, v, b);
    //@ open [?f] fset_internal(s, ?boxId);
    struct llnode* p = s->set;
    //@ int pvalue = p->value;

    mutex3_acquire(p->mutex);
    //@ close [f] fset_internal_ex(s, boxId, p, ?pm);
    // perform change(p, v) to get to link
    perform_change_head(s, v);

    //@ open [f] fset_internal_ex(s, boxId, p, pm);
    //@ open linkex(p, pm, ?pn, pvalue, v, ?pnm, ?pnv);
    struct llnode* c = p->next;
    int cvalue = c->value;
    //@ close linkex(p, pm, c, pvalue, v, pnm, cvalue);
    //@ close [f] fset_internal(s, boxId);
    while(cvalue < v) 
    /*@ invariant [f]fset_internal(s, boxId) &*& changeperm(?h, boxId, v, b, set_singleton(gnode(p, c, pvalue, v))) &*& 
            linkex(p, ?pmutex, c, pvalue, v, ?cmutex, cvalue) &*& v > INT_MIN &*& v < INT_MAX &*& pvalue < v;
    @*/
    {
        //@ open linkex(p, pmutex, c, pvalue, v, cmutex, cvalue);
        //@ open link_internal(p, pmutex, c, pvalue, v, cmutex, cvalue);
        mutex3_acquire(c->mutex);
        //@ close linkex(p, pmutex, c, pvalue, v, cmutex, cvalue);
        
        // perform change(c, v)
        perform_change_other(s, v, p, c);
        //@ assert linkex(c, cmutex, ?cn, cvalue, v, ?cnm, ?cnv);
        //@ assert changeperm(h, boxId, v, b, set_add(set_singleton(gnode(p, c, pvalue, v)), gnode(c, cn, cvalue, v)));
        //@ linkex_distinct(p, c);
        
        // save the mutex of p. After performing gap, we no longer have permission to read the mutex of p.        
        //@ open linkex(p, pmutex, c, pvalue, v, cmutex, cvalue);
        struct mutex3* pmut = p->mutex;
        //@ close linkex(p, pmut, c, pvalue, v, cmutex, cvalue);
        
        // perform gap1(p, c, v);
        perform_gap1(s, v, p);
        //@ assert changeperm(h, boxId, v, b, set_singleton(gnode(c, cn, cvalue, v)));

        mutex3_release(pmut);
        
        p = c;
        //@ pvalue = cvalue;
        c = c->next;
        cvalue = c->value;
    }
    
    //need observe action to get to values and show that mem(v, values) == (v == cvalue);
    perform_obs_mem(s, v, p);
    
    return p;
}

//TODO: while it may not be necessary, maybe we should keep a fraction of pvalue in link as well.


bool scontains(struct fset* s, int v) 
    //@requires own(s, v, ?m) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures own(s, v, result);
{
    struct llnode* p = slocate(s, v);
    
    //@ open linkex(p, ?pm, ?cur, ?pvalue, v, ?cm, ?cvalue);
    struct llnode* c = p->next;
    bool result = (c->value == v);
    //@ close linkex(p, pm, c, pvalue, v, cm, cvalue);
        
    // save the mutex of p. After performing gap, we no longer have permission to read the mutex of p.        
    //@ open linkex(p, pm, c, pvalue, v, cm, cvalue);
    struct mutex3* pmutex = p->mutex;
    //@ close linkex(p, pm, c, pvalue, v, cm, cvalue);
    
    perform_gap1(s, v, p);

    mutex3_release(pmutex);
    
    //@ close own(s, v, result);
    return result;
}


void sadd(struct fset* s, int v) 
    //@requires own(s, v, ?b) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures own(s, v, true);
{
    struct llnode* p = slocate(s, v);
    //@ open linkex(p, ?pm, ?cur, ?pvalue, v, ?cm, ?cvalue);
    struct llnode* c = p->next;
    struct mutex3* pmutex = p->mutex;
    if(c->value != v) {
        struct llnode* n = malloc(sizeof(struct llnode));
        if(n == 0) abort();
        struct mutex3* m = create_mutex3();
        mutex3_release(m);
        n->mutex = m;
        n->value = v;
        n->next = c;
        //@ n->owner = INT_MIN;
        //@ close node_internal(n, m, v, INT_MIN);
        //@ close linkex(n, m, c, v, INT_MIN, cm, cvalue);
        p->next = n;
        //@ close linkex(p, pmutex, n, pvalue, v, m, v);
        
        //perform gap2 to insert value
        perform_gap2(s, v, p);
        
        //@ assert mutex3_held(pmutex);
    } else {
        //@ close linkex(p, pmutex, c, pvalue, v, cm, cvalue);
        perform_gap1(s, v, p);
    }

    mutex3_release(pmutex);
    
    //@ close own(s, v, true);    
}

void sremove(struct fset* s, int v) 
    //@requires own(s, v, ?m) &*& v > INT_MIN &*& v < INT_MAX;
    //@ensures own(s, v, false);
{
    struct llnode* p = slocate(s, v);
    //@ open linkex(p, ?pm, ?cur, ?pvalue, v, ?cm, ?cvalue);
    struct llnode* c = p->next;
    struct mutex3* pmutex = p->mutex;
    if(c->value == v) {
        mutex3_acquire(c->mutex);
        // perform change(c, v)
        perform_change_other(s, v, p, c);
        //@ linkex_distinct(p, c);
        
        //@ open linkex(c, cm, ?cn, cvalue, v, ?cnm, ?cnv);
        struct llnode* n = c->next;
        p->next = n;
        
        //@ close linkex(p, pm, n, pvalue, v, cnm, cnv);
        //perform gap3
        perform_gap3(s, v, p, c);

        //@ open lockednode(c, v, v);
        //@ open node_internal(c, _, v, v);
        mutex3_dispose(c->mutex);
        free(c);
    } else {
        //@ close linkex(p, pmutex, c, pvalue, v, cm, cvalue);
        perform_gap1(s, v, p);
    }
    
    mutex3_release(pmutex);
    
    //@ close own(s, v, false);    
}
/*
int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]char_array(argv, argc);
    //@ ensures true;
{
    return 0;
}
*/