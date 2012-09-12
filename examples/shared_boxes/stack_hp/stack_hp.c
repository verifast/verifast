#include "stdlib.h"
#include "atomics.h"
#include "atomics_int.h"
#include "linkedlist.h"
//@ #include "raw_ghost_lists.gh"
//@ #include "ghost_lists.gh"
//@ #include "cperm.gh"
//@ #include "lmultisetandset.gh"


/*
General strategy:
1. An access hazard occurs when a thread access a memory location that could be freed by another thread.

   To prevent access hazards, you get a fraction of the node after a hazard pointer has been set and validated.
   
2. An ABA hazard occurs when a thread first performs a CAS on a memory location to guarantee that the data structure is 
   still in the 'same' state as it was before. Another thread may first change the state and then restore the value of the memory location.
   As a result, the value of the memory location may be the same, but the state of the datastructe can be changed.
   
   Currently, we do not prove linearisability, and therefore we need not deal with ABA-hazards. 
   The clue is some each hazard pointer will need some extra ghost state. 
   The operations on the data structure (in addition to the fact that allocNodes can not be reused) will maintain
   an extra invariant on this ghost state. This invariant may differ from use to use.
   
   For example, for the stack: 
   Each hazard pointer should also be associated with a list of nodes, prevNodes, 
   which starts with the value of the hazard pointer. In addition, this property must be added:
       mem(head(prevNodes), nodes) ? endsWith(nodes, prevNodes) : true
   If the value of head remains the same, head(nodes) == head(prevNodes) and therefore nodes == prevNodes.
   
Primitives for a library for hazard pointers:
   1. method: init_hpspace
      initialize the hazard pointer space and register a destructor for free objects (to be used when creating the data structure)
      
   2. method: destroy_hpspace
      Destroy the clients (to be used when disposing the data structure)

   3. method: create_client
      Allocate a client (or reuse an existing one)

   4. method:  dispose_client
      Deactivate a client 
      
   5. method: set_hazard_pointer:
      Set the hazard pointer of a client and release the previous hazard pointer if it was valid. 
      The new hazard pointer still needs to be validated.
      This can be used to implement reset_hazard_pointer.
      
   6. lemma: validate_hazard_pointer (to be used inside an atomic action):
      if you can prove that the value of the hazard pointer is still reachable and its ABA invariant holds, 
      then release a fraction of the object and set hpAlloc.
      
   7. lemma: object_not_free (to be used inside an atomic action):
      if you can prove that an object is popped or retired, then it can not be equal to a free object.
   
   8. method: retire_object
      add's the object to the list with retired object
      
   9. method: scan
      collects all hazard pointers + garbage collect retired objects
   
*/
//TODO: maybe remove popped nodes
//TODO: make abstraction from the data structure. In this way, one single hazard pointer library can be used for verifying stack and queue.
//TODO: prove linearisability
//TODO: add invariant for hpCount (e.g. hpCount >= length(allocated) )
//TODO: multiple hazard pointers
//TODO: dynamic number of hazard pointers with retiring
//TODO: Change the clients so that it can manage an arbitrary number of data structures.
//TODO: use hashmap/balanced tree in scanning algorithm

/*
NOTE: 
    - a global linked list with deleted nodes is impossible, since you again need a wait-free way to pop a node to delete it
      for similar reasons, a global with reclaimed nodes is impossible 
      what you can do is use one or more fields or an array with a fixed size (for the entire lifetime of the stack) to cache number of nodes. 
      The array may be through a pointer, but it is impossible to change the pointer and thus the size of the array.
*/

struct node {
    void *data;
    struct node *next;
    //@ int trackerId; //the id of the cptracker for this node
};

//Note: stack clients cannot be freed before the stack is disposed
struct stack_client {
    //TODO: turn this field into a boolean (how does this work with atomic_store????)
    void* active; //whether this stack_client is currently allocated by a thread
    
    struct linkedlist* rlist; //the linked list that contains the retired nodes of this thread 
    //@ list<struct node*> retiredNodes; // the retired nodes of this thread
    struct node* hp; //the current hazard pointer of this client (zero if unused)
    //@ bool hpAllocated; //whether the current hazard pointer was correctly allocated 
    struct stack_client* next; //the next stack client
    //@ struct stack* stack;
    //@ struct node* popped;
    //@ bool localHpActive; //whether this client is currently collecting the global hazard pointers
    //@ list<struct stack_client*> localHpRemClients; //the remaining stack clients for which the hazard pointers must be collected. 
    //@ bool localHpFirstCollected; //whether the hazard pointer of the first remaining stack client is collected. 
    //@ list<struct node*> localHpList; //the local hazard pointers
    //@ real stack_full_fraction_helper_fraction;
};

struct stack {
    struct node *head;
    struct stack_client* clients;
    //@ int allClientsId;
    //@ bool full_fraction_helper;
    int hpCount;
};


/*@

lemma void ghost_list_member_handle_lemma_helper<t>(int id, t x)
    requires ghost_list<t>(id, ?xs) &*& [?f]ghost_list_member_handle<t>(id, x);
    ensures ghost_list<t>(id, xs) &*& [f]ghost_list_member_handle<t>(id, x) &*& mem(x, xs) == true;
{
    ghost_list_member_handle_lemma();
}

lemma void foreach_remove_helper<t>(t x, list<t> xs, predicate (t) p)
    requires foreach(xs, p) &*& mem(x, xs) == true;
    ensures foreach(remove(x, xs), p) &*& p(x);
{
    foreach_remove(x, xs);
}
lemma void foreach_unremove_helper<t>(t x, list<t> xs, predicate (t) p)
    requires foreach(remove(x, xs), p) &*& mem(x, xs) == true &*& p(x);
    ensures foreach(xs, p);
{
    foreach_unremove(x, xs);
}
@*/

/*@

predicate node(struct node *node; struct node *next, void *data, int trackerId) = 
    malloc_block_node(node) &*&
    node != 0 &*&
    node->next |-> next &*&
    node->data |-> data &*&
    node->trackerId |-> trackerId;

//TODO: remove
predicate node_precursor(struct node *node; struct node *next, void *data, int trackerId) = 
    node(node, next, data, trackerId);

predicate node_cp_helper(struct node *node; pair<struct node*, pair<void*, int> > out) = 
    node(node, ?next, ?data, ?trackerId) &*&
    out == pair(next, pair(data, trackerId));

predicate tracked_node_fraction(struct node *node, struct node *next, void *data, real f) = 
    [f]node(node, next, data, ?trackerId) &*&
    cpticket(trackerId, ?tid, f) &*&
    f > 0;

predicate node_tracker(struct node *node, int id, int count) = 
    cptracker(id, node_cp_helper, node, count, ?out) &*&
    snd(snd(out)) == id;

lemma void node_precursor_tracked_node_fraction_distinct(struct node* n1, struct node* n2)
    requires node_precursor(n1, ?next, ?data, ?trackerId) &*& tracked_node_fraction(n2, ?n4, ?n2data, ?f);
    ensures node_precursor(n1, next, data, trackerId) &*& tracked_node_fraction(n2, n4, n2data, f) &*& n1 != n2;
{
    open tracked_node_fraction(n2, n4, n2data, f);
    open node_precursor(n1, next, data, trackerId);
    open node(n1, next, data, trackerId);
    open [f]node(n2, n4, n2data, ?n2trackerId);
    assert n1 != n2;
    close [f]node(n2, n4, n2data, n2trackerId);
    close node(n1, next, data, trackerId);
    close node_precursor(n1, next, data, trackerId);
    close tracked_node_fraction(n2, n4, n2data, f);
}
lemma void node_precursor_node_tracker_distinct(struct node* n1, struct node* n2)
    requires node_precursor(n1, ?next, ?data, ?trackerId) &*& node_tracker(n2, ?id, ?count);
    ensures node_precursor(n1, next, data, trackerId) &*& node_tracker(n2, id, count) &*& n1 != n2;
{
    if(n1 == n2) {
        open node_tracker(n2, id, count);
        open node_precursor(n1, next, data, trackerId);
        close node_cp_helper(n1, _);
        cptracker_match(id);
        open node_cp_helper(n1, _);
        open node(n1, _, _, _);
        int tid = create_cpticket(id);
        open [?f] node_cp_helper(n2, _);
        open [f] node(n2, _, _, _);
        assert false;
    }
}

predicate lseg(struct node *first, struct node *last, list<void *> nodes, list<void *> elems) =
    first == last ?
        nodes == nil &*&
        elems == nil
    :
        tracked_node_fraction(first, ?next, ?data, ?f) &*& 
        lseg(next, last, ?nodes0, ?elems0) &*&
        nodes == cons(first, nodes0) &*&
        elems == cons(data, elems0);

lemma void node_precursor_lseg_distinct(struct node* n1, list<struct node*> nodes)
    requires node_precursor(n1, ?next, ?data, ?trackerId) &*& lseg(?n2, ?n3, nodes, ?elems);
    ensures node_precursor(n1, next, data, trackerId) &*& lseg(n2, n3, nodes, elems) &*& !mem(n1, nodes);
{
    switch(nodes) {
        case nil:
            open lseg(n2, n3, nodes, elems);
            close lseg(n2, n3, nodes, elems);
        case cons(h, t):
            open lseg(n2, n3, nodes, elems);
            node_precursor_tracked_node_fraction_distinct(n1, n2);
            node_precursor_lseg_distinct(n1, t);
            close lseg(n2, n3, nodes, elems);
    }
}

predicate stack_client_precursor(struct stack_client *client; struct stack* stack, struct node* hp, bool hpAllocated, struct stack_client* next, struct node* popped, real frac) =
    client != 0 &*&
    malloc_block_stack_client(client) &*&
    client->hp |-> hp &*&
    client->hpAllocated |-> hpAllocated &*&
    client->stack |-> stack &*&
    client->next |-> next &*&
    client->popped |-> popped &*&
    client->active |-> (void*)1 &*& 
    client->rlist |-> ?rlist &*&
    client->retiredNodes |-> nil &*&
    client->localHpList |-> nil &*&
    client->localHpActive |-> false &*&
    client->localHpRemClients |-> nil &*&
    client->localHpFirstCollected |-> false &*&
    client->stack_full_fraction_helper_fraction |-> frac &*& 
    frac > 0 &*&
    [frac]stack->full_fraction_helper |-> _ &*&
    linkedlist(rlist, nil);

predicate stack_client_int(struct stack_client *client, int allClientsId, struct stack* stack, struct node* hp, bool allocated, struct node* popped, list<struct node*>retired, bool hpActive, list<struct stack_client*> hpRem, list<struct node*>hpList, bool fcc, real frac) = 
    client != 0 &*&
    [1/2]client->active |-> (void*)1 &*&
    [1/2]client->hp |-> hp &*&
    [1/2]client->stack |-> stack &*&
    [1/2]client->hpAllocated |-> allocated  &*&
    [1/2]client->popped |-> popped &*&
    [1/2]client->localHpList |-> hpList &*&
    [1/2]client->localHpActive |-> hpActive &*&
    [1/2]client->localHpRemClients |-> hpRem &*&
    [1/2]client->localHpFirstCollected |-> fcc &*&
    [1/2]client->retiredNodes |-> retired &*&
    [1/2]client->stack_full_fraction_helper_fraction |-> frac &*& 
    frac > 0 &*&
    [_]ghost_list_member_handle(allClientsId, client);

predicate stack_client(struct stack_client *client, int allClientsId, struct stack* stack, struct node* hp, bool allocated, struct node* popped, real frac) = 
    stack_client_int(client, allClientsId, stack, hp, allocated, popped, ?retiredNodes, false, nil, nil, false, frac) &*&
    client->rlist |-> ?rlist &*&
    linkedlist(rlist, retiredNodes);

predicate stack_client_internal(struct stack_client *client, int allClientsId, struct stack* stack, struct node* hp, struct stack_client* next, bool allocated, struct node* popped, list<struct node*> retired, list<struct node*> lhp, bool lhpActive, list<struct stack_client*> lhpRem, bool fcc, bool active) = 
    client != 0 &*&
    malloc_block_stack_client(client) &*&
    [1/2]client->active |-> (active ? (void*)1 : (void*)0) &*&
    [1/2]client->hp |-> hp &*&
    [1/2]client->hpAllocated |-> allocated &*&
    [1/2]client->stack |-> stack &*&
    [1/2]client->popped |-> popped &*&
    [1/2]client->localHpActive |-> lhpActive &*&
    [1/2]client->localHpRemClients |-> lhpRem &*&
    [1/2]client->localHpList |-> lhp &*&
    [1/2]client->localHpFirstCollected |-> fcc &*&
    [1/2]client->retiredNodes |-> retired &*&
    [1/2]client->stack_full_fraction_helper_fraction |-> ?frac &*& 
    frac > 0 &*&
    client->next |-> next &*&
    [_]ghost_list_member_handle(allClientsId, client) &*&
    (active ? 
        [frac]stack->full_fraction_helper |-> _ 
        : 
        [1/2]client->active |-> _ &*&
        [1/2]client->hp |-> 0 &*&
        [1/2]client->hpAllocated |-> false &*&
        [1/2]client->stack |-> _ &*&
        [1/2]client->popped |-> 0 &*&
        [1/2]client->localHpActive |-> false &*&
        [1/2]client->localHpRemClients |-> nil &*&
        [1/2]client->localHpList |-> nil &*&
        [1/2]client->localHpFirstCollected |-> false &*&
        [1/2]client->retiredNodes |-> _ &*&
        [1/2]client->stack_full_fraction_helper_fraction |-> _ &*&
        client->rlist |-> ?rlist &*&
        linkedlist(rlist, retired)
        );

lemma void stack_client_match(struct stack_client* client)
    requires stack_client_int(client, ?allClientsId, ?stack, ?hp, ?hpAllocated, ?popped, ?retired, ?lhpActive, ?lhpRem, ?lhpList, ?fcc, ?f1) &*&
         stack_client_internal(client, ?allClientsId2, ?stack2, ?hp2, ?c1Next, ?hpAllocated2, ?popped2, ?retired2, ?lhpList2, ?lhpActive2, ?lhpRem2, ?fcc2, ?active);
    ensures  stack_client_int(client, allClientsId, stack, hp, hpAllocated, popped, retired, lhpActive, lhpRem, lhpList, fcc, f1) &*&
         stack_client_internal(client, allClientsId2, stack2, hp2, c1Next, hpAllocated2, popped2, retired2, lhpList2, lhpActive2, lhpRem2, fcc2, active) &*&
          stack == stack2 &*& hp == hp2 &*& hpAllocated == hpAllocated2 &*&
         popped == popped2 &*& retired == retired2 &*& lhpActive == lhpActive2 &*& lhpRem == lhpRem2 &*& lhpList == lhpList2 &*&
         fcc == fcc2 &*& active == true;
{
    open stack_client_int(client, allClientsId, stack, hp, hpAllocated, popped, retired, lhpActive, lhpRem, lhpList, fcc, f1);
    open stack_client_internal(client, allClientsId2, stack2, hp2, c1Next, hpAllocated2, popped2, retired2, lhpList2, lhpActive2, lhpRem2, fcc2, active);
    close stack_client_int(client, allClientsId, stack, hp, hpAllocated, popped, retired, lhpActive, lhpRem, lhpList, fcc, f1);
    close stack_client_internal(client, allClientsId2, stack2, hp2, c1Next, hpAllocated2, popped2, retired2, lhpList2, lhpActive2, lhpRem2, fcc2, active);
}
lemma void stack_client_match2(struct stack_client* client)
    requires stack_client_int(client, ?allClientsId,  ?stack,  ?hp,  ?hpAllocated,  ?popped,  ?retired,  ?lhpActive, ?lhpRem, ?lhpList, ?fcc, ?f) &*&
             stack_client_int(client, ?allClientsId2, ?stack2, ?hp2, ?hpAllocated2, ?popped2, ?retired2, ?lhpActive2, ?lhpRem2, ?lhpList2, ?fcc2, ?f2);
    ensures  stack_client_int(client, allClientsId, stack, hp, hpAllocated, popped, retired, lhpActive, lhpRem, lhpList, fcc, f) &*&
         stack_client_int(client, allClientsId2, stack2, hp2, hpAllocated2, popped2, retired2, lhpActive2, lhpRem2, lhpList2, fcc2, f2) &*&
         stack == stack2 &*& hp == hp2 &*& hpAllocated == hpAllocated2 &*&
         popped == popped2 &*& retired == retired2 &*& lhpActive == lhpActive2 &*& lhpRem == lhpRem2 &*& lhpList == lhpList2 &*&
         fcc == fcc2 &*& f == f2;
{
    open stack_client_int(client, allClientsId, stack, hp, hpAllocated, popped, retired, lhpActive, lhpRem, lhpList, fcc, f);
    open stack_client_int(client, allClientsId2, stack2, hp2, hpAllocated2, popped2, retired2, lhpActive2, lhpRem2, lhpList2, fcc2, f2);
    close stack_client_int(client, allClientsId, stack, hp, hpAllocated, popped, retired, lhpActive, lhpRem, lhpList, fcc, f);
    close stack_client_int(client, allClientsId2, stack2, hp2, hpAllocated2, popped2, retired2, lhpActive2, lhpRem2, lhpList2, fcc2, f2);
}    

inductive hpRec = hpRec(list<struct stack_client*>, list<struct node*>, list<struct node*>, bool);
fixpoint list<struct stack_client*> remClients(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return rem; } }
fixpoint list<struct node*> validNodes(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return valid; } }
fixpoint list<struct node*> hpNodes(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return hps; } }
fixpoint bool firstCollected(hpRec r) { switch(r) { case hpRec(rem, valid, hps, first): return first; } }


predicate clients(struct stack_client *first, struct stack_client *last, int allClientsId, struct stack* stack, list<struct stack_client*> clients, list<struct node *> nodes, list<struct node *> poppedNodes, list<struct node*> retiredNodes, list<hpRec> localHpRecs) =
    first == last ?
        nodes == nil &*&
        clients == nil &*&
        poppedNodes == nil &*&
        localHpRecs == nil &*&
        retiredNodes == nil
    :
        stack_client_internal(first, allClientsId, stack, ?hp, ?next, ?allocated, ?popped, ?retired, ?lhp, ?lhpA, ?lhpR, ?fcc, ?active) &*& 
        clients(next, last, allClientsId, stack, ?clients0, ?nodes0, ?poppedNodes0, ?retiredNodes0, ?localHpRecs0) &*&
        nodes == cons((allocated ? hp : 0), nodes0) &*&
        (popped != 0 ? poppedNodes == cons(popped, poppedNodes0) : poppedNodes == poppedNodes0) &*&
        (lhpA ? localHpRecs == cons(hpRec(lhpR, retired, lhp, fcc), localHpRecs0) : localHpRecs == localHpRecs0)&*&
        retiredNodes == append(retired, retiredNodes0) &*&
        clients == cons(first, clients0);

fixpoint bool containsValidNode(list<hpRec> recs, struct node* n) {
    switch(recs) {
        case nil: return false;
        case cons(r, t):
            return mem(n, validNodes(r)) || containsValidNode(t, n);
    }
}

lemma void clients_not_containsValidNode(list<hpRec> hprs, struct node* n) 
   requires clients(?from, ?to, ?id, ?stack, ?all, ?nodes, ?popped, ?retired, hprs) &*& !mem(n, retired);
   ensures clients(from, to, id, stack, all, nodes, popped, retired, hprs) &*& !containsValidNode(hprs, n);
{
    if(from == to) {
        open clients(from, to, id, stack, all, nodes, popped, retired, hprs);
        close clients(from, to, id, stack, all, nodes, popped, retired, hprs);
    } else {
        open clients(from, to, id, stack, all, nodes, popped, retired, hprs);
        open stack_client_internal(from, _, _, _, ?next, _, _, ?ret, _, _, _, _, ?active);
        close stack_client_internal(from, _, _, _, next, _, _, ret, _, _, _, _, active);
        assert clients(next, to, id, _, _, _, _, ?nretired, ?nhprs);
        mem_append(n, ret, nretired);
        clients_not_containsValidNode(nhprs, n);
        assert !containsValidNode(nhprs, n);
        close clients(from, to, id, stack, all, nodes, popped, retired, hprs);
    }
}

lemma void clients_length(struct stack_client *first, struct stack_client *last)
    requires clients(first, last, ?allClientsId, ?stack, ?clients, ?nodes, ?popped, ?retired, ?hpLists);
    ensures clients(first, last, allClientsId, stack, clients, nodes, popped, retired, hpLists) &*& length(clients) == length(nodes);
{
    if(first == last) {
        open clients(first, last, allClientsId, stack, clients, nodes, popped, retired, hpLists);
        close clients(first, last, allClientsId, stack, clients, nodes, popped, retired, hpLists);
    } else {
        open clients(first, last, allClientsId, stack, clients, nodes, popped, retired, hpLists);
        assert stack_client_internal(first, _, stack, _, ?next, _, _, _, _, _, _, _, _);
        clients_length(next, last);
        close clients(first, last, allClientsId, stack, clients, nodes, popped, retired, hpLists);
    }
}


lemma void clients_split(struct stack_client *first, struct stack_client *client)
    requires clients(first, 0, ?allClientsId, ?stack, ?clients, ?nodes, ?popped, ?retired, ?hplists) &*& mem(client, clients) == true &*& client != 0;
    ensures clients(first, client, allClientsId, stack, ?clients1, ?nodes1, ?popped1, ?retired1, ?hplists1) &*& 
            clients(client, 0, allClientsId, stack, ?clients2, ?nodes2, ?popped2, ?retired2, ?hplists2) &*& 
        clients == append(clients1, clients2) &*& nodes == append(nodes1, nodes2) &*& popped == append(popped1, popped2) &*&
        hplists == append(hplists1, hplists2) &*& retired == append(retired1, retired2) &*&
        !mem(client, clients1);
{
    if(first == 0) {
        open clients(first, 0, allClientsId, stack, clients, nodes, popped, _, _);
        assert false; 
    } else {
        open clients(first, 0, allClientsId, stack, clients, nodes, popped, _, _);
        if(first == client) {
            close clients(first, 0, allClientsId, stack, clients, nodes, popped, _, _);
            close clients(first, first, allClientsId, stack, nil, nil, nil, _, _);
        } else {
            assert stack_client_internal(first, allClientsId, stack, ?hp, ?next, ?allocated, ?p, ?ret, _, _, _, _, _);
            clients_split(next, client);
            assert clients(next, client, allClientsId, stack, _, _, _, ?retired1, _) &*& clients(client, 0, allClientsId, stack, _, _, _, ?retired2, _);
            close clients(first, client, allClientsId, stack, _, _, _, _, _);
            
            append_assoc(ret, retired1, retired2);
        }
    }
}

lemma void clients_split2(struct stack_client *first, struct stack_client *client, struct stack_client *last)
    requires clients(first, last, ?allClientsId, ?stack, ?clients, ?nodes, ?popped, ?retired, ?hplists) &*& mem(client, clients) == true &*& !mem(last, clients);
    ensures clients(first, client, allClientsId, stack, ?clients1, ?nodes1, ?popped1, ?retired1, ?hplists1) &*& 
            clients(client, last, allClientsId, stack, ?clients2, ?nodes2, ?popped2, ?retired2, ?hplists2) &*& 
        clients == append(clients1, clients2) &*& nodes == append(nodes1, nodes2) &*& popped == append(popped1, popped2) &*&
        hplists == append(hplists1, hplists2) &*& retired == append(retired1, retired2) &*&
        !mem(client, clients1);
{
    if(first == last) {
        open clients(first, last, allClientsId, stack, clients, nodes, popped, _, _);
        assert false; 
    } else {
        open clients(first, last, allClientsId, stack, clients, nodes, popped, _, _);
        if(first == client) {
            close clients(first, last, allClientsId, stack, clients, nodes, popped, _, _);
            close clients(first, first, allClientsId, stack, nil, nil, nil, _, _);
        } else {
            assert stack_client_internal(first, allClientsId, stack, ?hp, ?next, ?allocated, ?p, ?ret, _, _, _, _, _);
            clients_split2(next, client, last);
            assert clients(next, client, allClientsId, stack, _, _, _, ?retired1, _) &*& clients(client, last, allClientsId, stack, _, _, _, ?retired2, _);
            close clients(first, client, allClientsId, stack, _, _, _, _, _);
            
            append_assoc(ret, retired1, retired2);
        }
    }
}

lemma void clients_join(struct stack_client *first)
    requires clients(first, ?client, ?allClientsId, ?stack, ?clients1, ?nodes1, ?popped1, ?retired1, ?hplists1) &*& 
             clients(client, 0, allClientsId, stack, ?clients2, ?nodes2, ?popped2, ?retired2, ?hplists2);
    ensures clients(first, 0, allClientsId, stack, append(clients1, clients2), append(nodes1, nodes2), append(popped1, popped2), append(retired1, retired2), append(hplists1, hplists2));
{
    if(first == client) {
        open clients(first, client, allClientsId, stack, _, _, _, _, _);
    } else {
        open clients(first, client, allClientsId, stack, _, _, _, _, _);
        assert stack_client_internal(first, allClientsId, stack, ?hp, ?next, ?allocated, ?p, _, _, _, _, _, _);
        assert clients(next, client, allClientsId, stack, ?clients1b, ?nodes1b, ?popped1b, ?retired1b, ?hplists1b);
        clients_join(next);
        open stack_client_internal(first, allClientsId, stack, hp, next, allocated, p, ?ret, ?hplist, _, _, _, ?active);
        assert first != 0;
        close stack_client_internal(first, allClientsId, stack, hp, next, allocated, p, ret, hplist, _, _, _, active);
        append_assoc(ret, retired1b, retired2);
        close clients(first, 0, allClientsId, stack, _, _, _, _, _);
    }
}

lemma void clients_join2(struct stack_client *first, struct stack_client *last)
    requires clients(first, ?client, ?allClientsId, ?stack, ?clients1, ?nodes1, ?popped1, ?retired1, ?hplists1) &*& 
             clients(client, last, allClientsId, stack, ?clients2, ?nodes2, ?popped2, ?retired2, ?hplists2) &*& !mem(last, clients1);
    ensures clients(first, last, allClientsId, stack, append(clients1, clients2), append(nodes1, nodes2), append(popped1, popped2), append(retired1, retired2), append(hplists1, hplists2));
{
    if(first == client) {
        open clients(first, client, allClientsId, stack, _, _, _, _, _);
    } else {
        open clients(first, client, allClientsId, stack, _, _, _, _, _);
        assert stack_client_internal(first, allClientsId, stack, ?hp, ?next, ?allocated, ?p, _, _, _, _, _, _);
        assert clients(next, client, allClientsId, stack, ?clients1b, ?nodes1b, ?popped1b, ?retired1b, ?hplists1b);
        clients_join2(next, last);
        assert stack_client_internal(first, allClientsId, stack, hp, next, allocated, p, ?ret, ?hplist, _, _, _, ?active);
        assert first != last;
        //close stack_client_internal(first, allClientsId, stack, hp, next, allocated, p, ret, hplist, _, _, _, active);
        append_assoc(ret, retired1b, retired2);
        close clients(first, last, allClientsId, stack, _, _, _, _, _);
    }
}
lemma void clients_last_nomem(struct stack_client *first, struct stack_client *last)
    requires clients(first, last, ?allClientsId, ?stack, ?clients, ?nodes, ?popped, ?retired, ?hpLists);
    ensures clients(first, last, allClientsId, stack, clients, nodes, popped, retired, hpLists) &*& !mem(last,clients);
{
    if(first == last) {
        open clients(first, last, allClientsId, stack, _, _, _, _, _);
        close clients(first, last, allClientsId, stack, _, _, _, _, _);
    } else {
        open clients(first, last, allClientsId, stack, _, _, _, _, _);
        assert stack_client_internal(first, allClientsId, stack, ?hp, ?next, ?allocated, ?p, _, _, _, _, _, _);
        assert clients(next, last, allClientsId, stack, ?clients1b, ?nodes1b, ?popped1b, ?retired1b, ?hplists1b);
        clients_last_nomem(next, last);
        close clients(first, last, allClientsId, stack, _, _, _, _, _);
    }
}
lemma void clients_distinct(struct stack_client *first)
    requires clients(first, 0, ?allClientsId, ?stack, ?clients, ?nodes, ?popped, ?retired, ?hpLists);
    ensures clients(first, 0, allClientsId, stack, clients, nodes, popped, retired, hpLists) &*& distinct(clients) == true;
{
    if(first == 0) {
        open clients(first, 0, allClientsId, stack, clients, nodes, popped, retired, hpLists);
        close clients(first, 0, allClientsId, stack, clients, nodes, popped, retired, hpLists);
    } else {
        open clients(first, 0, allClientsId, stack, clients, nodes, popped, retired, hpLists);
        assert stack_client_internal(first, _, stack, _, ?next, _, _, _, _, _, _, _, _);
        assert clients(next, 0, allClientsId, stack, ?nclients, _, _, _, _);
        clients_distinct(next);
        assert distinct(nclients) == true;
        if(mem(first, nclients)) {
            clients_split(next, first);
            open clients(first, 0, _, stack, _, _, _, _, _);
            open stack_client_internal(first, _, stack, _, _, _, _, _, _, _, _, _, _);
            open stack_client_internal(first, _, stack, _, _, _, _, _, _, _, _, _, _);
            assert false;
        }
        assert !mem(first, nclients);
        close clients(first, 0, allClientsId, stack, clients, nodes, popped, retired, hpLists);
    }
}

predicate_ctor node_tracker_helper(list<struct node*> allocNodes, int extra)(struct node* node) = 
    node_tracker(node, ?id, occ(allocNodes, node) + extra);

lemma void node_precursor_node_tracker_helper_distinct(struct node* n1, struct node* n2, list<struct node*> allocNodes, int extra)
    requires node_precursor(n1, ?next, ?data, ?trackerId) &*& node_tracker_helper(allocNodes, extra)(n2);
    ensures node_precursor(n1, next, data, trackerId) &*& node_tracker_helper(allocNodes, extra)(n2) &*& n1 != n2;
{
    open node_tracker_helper(allocNodes, extra)(n2);
    node_precursor_node_tracker_distinct(n1, n2);
    close node_tracker_helper(allocNodes, extra)(n2);
}

lemma void node_precursor_foreach_node_tracker_helper_distinct(struct node* n1, list<struct node*> nodes, list<struct node*> allocNodes, int extra)
    requires node_precursor(n1, ?next, ?data, ?trackerId) &*& foreach(nodes, node_tracker_helper(allocNodes, extra));
    ensures node_precursor(n1, next, data, trackerId) &*& foreach(nodes, node_tracker_helper(allocNodes, extra)) &*& !mem(n1, nodes);
{
    if(mem(n1,nodes)) {
        foreach_remove(n1, nodes);
        node_precursor_node_tracker_helper_distinct(n1, n1, allocNodes, extra);
    }
}

predicate validLhp(list<struct stack_client*> allClients, list<struct node*> allocNodes, list<struct node*> retiredNodes, list<struct stack_client*> lhpRem, list<struct node*> lhpValid, list<struct node*> lhp, bool fcc) =
    length(allClients) == length(allocNodes) &*&
    length(lhpRem) <= length(allClients) &*&
    (fcc ? lhpRem != nil : true) &*& 
    lhpRem == drop(length(allClients) - length(lhpRem), allClients) &*& 
    !mem((struct node*)0, lhpValid) &*&
    lset_subset(lhpValid, retiredNodes) == true &*&
    lset_subset(lset_inters(take(length(allocNodes) - length(lhpRem) + (fcc ? 1 : 0), allocNodes), lhpValid), lset_inters(lhp, lhpValid)) == true;

predicate_ctor validLhp_helper(list<struct stack_client*> allClients, list<struct node*> allocNodes, list<struct node*> retiredNodes)(hpRec lhpR) = 
    validLhp(allClients, allocNodes, retiredNodes, remClients(lhpR), validNodes(lhpR), hpNodes(lhpR), firstCollected(lhpR));
     
predicate stackInternal(struct stack *stack, list<void *> elems, int allClientsId) =
    malloc_block_stack(stack) &*&
    stack->head |-> ?head &*& 
    lseg(head, 0, ?nodes, elems) &*&
    stack->clients |-> ?clients &*&
    [1/2]stack->allClientsId |-> allClientsId &*& 
    clients(clients, 0, allClientsId, stack, ?clientsList, ?allocNodes, ?poppedNodes, ?retiredNodes, ?lhpRs) &*& 
    ghost_list<struct stack_client*>(allClientsId, clientsList) &*&
    stack->hpCount |-> ?hpCount &*& hpCount >= 0 &*& //TODO: hpCount >= length(allocNodes) &*&
    foreach(nodes, node_tracker_helper(allocNodes, 1)) &*&
    foreach(retiredNodes, node_tracker_helper(allocNodes, 0)) &*&
    foreach(poppedNodes, node_tracker_helper(allocNodes, 0)) &*&
    foreach(lhpRs, validLhp_helper(clientsList, allocNodes, retiredNodes)) &*&
    !mem<struct node*>(0, nodes) &*&
    !mem<struct node*>(0, retiredNodes) &*&
    !mem<struct node*>(0, poppedNodes) &*&
    distinct(nodes) == true &*&
    distinct(poppedNodes) == true &*&
    distinct(retiredNodes) == true &*&
    lset_disjoint(nodes, retiredNodes) == true &*&
    lset_disjoint(nodes, poppedNodes) == true &*&
    lset_disjoint(poppedNodes, retiredNodes) == true &*&
    lset_subset(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes))) == true;

predicate_ctor stack_ctor(struct stack *stack, int allClientsId) () = 
    stackInternal(stack, ?elems, allClientsId);
    
predicate stack_helper(struct stack *stack, int allClientsId) = 
    stack != 0 &*&
    [1/2]stack->allClientsId |-> allClientsId &*&
    atomic_space(stack_ctor(stack, allClientsId));

predicate stack_free(struct stack *stack) = 
    stack_helper(stack, ?allClientsId) &*&
    stack->full_fraction_helper |-> _;

predicate stack_with_client(struct stack *stack, struct stack_client* client, real frac) =
    [frac]stack_helper(stack, ?allClientsId) &*&
    stack_client(client, allClientsId, stack, 0, false, 0, frac);

lemma void updateAllocNodes_helper(list<struct node*> l, list<struct node*> l1, list<struct node*> l2, int extra, struct node* n)
    requires foreach(l, node_tracker_helper(append(l1, l2), extra)) &*& !mem(n, l);
    ensures foreach(l, node_tracker_helper(append(l1, cons(n, l2)), extra));
{
    switch(l) {
        case nil:
            open foreach(l, node_tracker_helper(append(l1, l2), extra));
            close foreach(l, node_tracker_helper(append(l1, cons(n, l2)), extra));
        case cons(h, t):
            assert h != n;
            open foreach(l, node_tracker_helper(append(l1, l2), extra));
            updateAllocNodes_helper(t, l1, l2, extra, n);
            open node_tracker_helper(append(l1, l2), extra)(h);
            occ_append(l1, l2, h);
            occ_append(l1, cons(n, l2), h);
            close node_tracker_helper(append(l1, cons(n, l2)), extra)(h);
            close foreach(l, node_tracker_helper(append(l1, cons(n, l2)), extra));
            
    }
}    
lemma void updateAllocNodes_helper2(list<struct node*> l, list<struct node*> l1, list<struct node*> l2, int extra, struct node* n)
    requires foreach(l, node_tracker_helper(append(l1, cons(n, l2)), extra)) &*& !mem(n, l);
    ensures foreach(l, node_tracker_helper(append(l1, l2), extra));
{
    switch(l) {
        case nil:
            open foreach(l, node_tracker_helper(append(l1, cons(n, l2)), extra));
            close foreach(l, node_tracker_helper(append(l1, l2), extra));
        case cons(h, t):
            assert h != n;
            open foreach(l, node_tracker_helper(append(l1, cons(n, l2)), extra));
            updateAllocNodes_helper2(t, l1, l2, extra, n);
            open node_tracker_helper(append(l1, cons(n, l2)), extra)(h);
            occ_append(l1, l2, h);
            occ_append(l1, cons(n, l2), h);
            close node_tracker_helper(append(l1, l2), extra)(h);
            close foreach(l, node_tracker_helper(append(l1, l2), extra));
            
    }
}
    
lemma void updateAllocNodes_helper3(list<struct node*> l, list<struct node*> l2, int extra, struct node* n)
    requires foreach(l, node_tracker_helper(l2, extra)) &*& !mem(n, l);
    ensures foreach(l, node_tracker_helper(cons(n, l2), extra));
{
    switch(l) {
        case nil:
            open foreach(l, node_tracker_helper(l2, extra));
            close foreach(l, node_tracker_helper(cons(n, l2), extra));
        case cons(h, t):
            assert h != n;
            open foreach(l, node_tracker_helper(l2, extra));
            updateAllocNodes_helper3(t, l2, extra, n);
            open node_tracker_helper(l2, extra)(h);
            close node_tracker_helper(cons(n, l2), extra)(h);
            close foreach(l, node_tracker_helper(cons(n, l2), extra));
            
    }

}
lemma void updateAllocNodes_helper4(list<struct node*> l, list<struct node*> l1, list<struct node*> l2, int extra, struct node* n1, struct node* n2)
    requires foreach(l, node_tracker_helper(append(l1, cons(n1, l2)), extra)) &*& !mem(n1, l) &*& !mem(n2, l);
    ensures foreach(l, node_tracker_helper(append(l1, cons(n2, l2)), extra));
{
    switch(l) {
        case nil:
            open foreach(l, node_tracker_helper(append(l1, cons(n1, l2)), extra));
            close foreach(l, node_tracker_helper(append(l1, cons(n2, l2)), extra));
        case cons(h, t):
            open foreach(l, node_tracker_helper(append(l1, cons(n1, l2)), extra));
            updateAllocNodes_helper4(t, l1, l2, extra, n1, n2);
            open node_tracker_helper(append(l1, cons(n1, l2)), extra)(h);
            occ_append(l1, cons(n1, l2), h);
            occ_append(l1, cons(n2, l2), h);
            close node_tracker_helper(append(l1, cons(n2, l2)), extra)(h);
            close foreach(l, node_tracker_helper(append(l1, cons(n2, l2)), extra));
            
    }
}    

lemma void validLhp_insert_retired(list<struct stack_client*> allClients, list<struct node*> alloc, list<struct node*> retired1, struct node* n, list<struct node*> retired2)
    requires validLhp(allClients, alloc, append(retired1, retired2), ?rem, ?lhpValid, ?lhps, ?fcc);
    ensures validLhp(allClients, alloc, append(retired1, cons(n, retired2)), rem, lhpValid, lhps, fcc);
{
    open validLhp(allClients, alloc, append(retired1, retired2), rem, lhpValid, lhps, fcc);
    if(!lset_subset(lhpValid, append(retired1, cons(n, retired2)))) {
        lset_subset_contains_conv(lhpValid, append(retired1, cons(n, retired2)));
        open exwitness(?x);
        lset_union_contains(retired1, cons(n, retired2), x);
        lset_subset_contains(lhpValid, append(retired1, retired2), x);
        lset_union_contains(retired1, retired2, x);
        assert false;
    }
    close validLhp(allClients, alloc, append(retired1, cons(n, retired2)), rem, lhpValid, lhps, fcc);
}

lemma void validLhp_cons_alloc(list<struct stack_client*> allClients, list<struct node*> alloc, list<struct node*> retired, struct node* n, struct stack_client* c)
    requires validLhp(allClients, alloc, retired, ?lhpRem, ?lhpValid, ?lhps, ?fcc) &*& !mem(n, retired);
    ensures validLhp(cons(c, allClients), cons(n, alloc), retired, lhpRem, lhpValid, lhps, fcc);
{
    open validLhp(allClients, alloc, retired, lhpRem, lhpValid, lhps, fcc);
    int rem = length(lhpRem) - (fcc ? 1 : 0);
    list<struct node *> newAlloc = cons(n, alloc);
    list<struct node *> l1 = take(length(newAlloc) - rem, newAlloc);
    list<struct node *> l2 = take(length(alloc) - rem, alloc);
    assert l1 == cons(n, l2);
    lset_subset_contains(lhpValid, retired, n);
    assert !mem(n, lhpValid);
    if(!lset_subset(lset_inters(l1, lhpValid), lset_inters(lhps, lhpValid))) {
        lset_subset_contains_conv(lset_inters(l1, lhpValid), lset_inters(lhps, lhpValid));
        open exwitness(?x);
        lset_inters_contains(l1, lhpValid, x);
        lset_subset_contains(lset_inters(l2, lhpValid), lset_inters(lhps, lhpValid), x);
        lset_inters_contains(l2, lhpValid, x);
        assert false;
    }
    close validLhp(cons(c, allClients), newAlloc, retired, lhpRem, lhpValid, lhps, fcc);
}
    
lemma void validLhp_replace_alloc(list<struct stack_client*> allClients, list<struct node*> alloc1, struct node* n1, struct node* n2, list<struct node*> alloc2, list<struct node*> retired)
    requires validLhp(allClients, append(alloc1, cons(n1, alloc2)), retired, ?lhpRem, ?lhpValid, ?lhps, ?fcc) &*& !mem(n2, retired);
    ensures validLhp(allClients, append(alloc1, cons(n2, alloc2)), retired, lhpRem, lhpValid, lhps, fcc);
{
    open validLhp(allClients, append(alloc1, cons(n1, alloc2)), retired, lhpRem, lhpValid, lhps, fcc);
    lset_subset_contains(lhpValid, retired, n2);
    assert !mem(n2, lhpValid);
    int rem = length(lhpRem) - (fcc ? 1 : 0);    
    list<struct node*> l1 = append(alloc1, cons(n1, alloc2));
    list<struct node*> l2 = append(alloc1, cons(n2, alloc2));
    list<struct node*> k1 = take(length(l1) - rem, l1);
    list<struct node*> k2 = take(length(l2) - rem, l2);
    if(!lset_subset(lset_inters(k2, lhpValid), lset_inters(lhps, lhpValid))) {
        lset_subset_contains_conv(lset_inters(k2, lhpValid), lset_inters(lhps, lhpValid));
        open exwitness(?x);
        assert lset_contains(lset_inters(k2, lhpValid), x) == true;
        assert lset_contains(lset_inters(lhps, lhpValid), x) == false;        
        lset_inters_contains(k2, lhpValid, x);
        assert lset_contains(k2, x) == true;
        assert lset_contains(lhpValid, x) == true;
        take_append(length(l1) - rem, alloc1, cons(n1, alloc2));
        take_append(length(l2) - rem, alloc1, cons(n2, alloc2));
        lset_subset_contains(lset_inters(k1, lhpValid), lset_inters(lhps, lhpValid), x);
        lset_inters_contains(k1, lhpValid, x);
        if(length(l1)-rem > length(alloc1)) {
            lset_union_contains(alloc1, take(length(l1) - rem - length(alloc1), cons(n1, alloc2)), x);
            lset_union_contains(alloc1, take(length(l1) - rem - length(alloc1), cons(n2, alloc2)), x);
        } 
        assert false;
    }
    close validLhp(allClients, append(alloc1, cons(n2, alloc2)), retired, lhpRem, lhpValid, lhps, fcc);
}

lemma void validLhp_process_client(list<struct node*> alloc1, struct node* h, list<struct node*> alloc2, struct node* hp)
    requires validLhp(?allClients, append(alloc1, cons(h, alloc2)), ?retired, ?lhpRem, ?lhpValid, ?lhp, false) &*& 
             length(lhpRem) == length(cons(h, alloc2)) &*&
             (h == 0 ? true : h == hp);
    ensures  validLhp(allClients, append(alloc1, cons(h, alloc2)), retired,  lhpRem,  lhpValid, (hp == 0 ? lhp : cons(hp, lhp)), true);
{
    open validLhp(allClients, append(alloc1, cons(h, alloc2)), retired, lhpRem, lhpValid, lhp, false);
    list<struct node*> allocNodes = append(alloc1, cons(h, alloc2));
    list<struct node*> newLhp = (hp == 0 ? lhp : cons(hp, lhp));
    int rem = length(lhpRem);
    int newRem = length(lhpRem) - 1;
    assert length(allocNodes) - rem == length(alloc1);
    assert length(allocNodes) - newRem == length(alloc1) + 1;
    list<struct node*> l1 = take(length(allocNodes) - rem, allocNodes);
    list<struct node*> l2 = take(length(allocNodes) - newRem, allocNodes);
    take_append(length(alloc1), alloc1, cons(h, alloc2));
    assert l1 == alloc1;
    take_append(length(alloc1) + 1, alloc1, cons(h, alloc2));
    assert l2 == append(l1, cons(h, nil));
    
    if(!lset_subset(lset_inters(l2, lhpValid), lset_inters(newLhp, lhpValid))) {
        lset_subset_contains_conv(lset_inters(l2, lhpValid), lset_inters(newLhp, lhpValid));
        open exwitness(?x);
        lset_inters_contains(l2, lhpValid, x);
        lset_inters_contains(newLhp, lhpValid, x);
        lset_subset_contains(lset_inters(l1, lhpValid), lset_inters(lhp, lhpValid), x);
        lset_inters_contains(l1, lhpValid, x);
        lset_inters_contains(lhp, lhpValid, x);
        lset_union_contains(l1, cons(h, nil), x);
        assert false;
    }
    close validLhp(allClients, append(alloc1, cons(h, alloc2)), retired,  lhpRem,  lhpValid, newLhp, true);
}    

lemma void validLhp_next_client(list<struct stack_client*> hpRem)
    requires validLhp(?allClients, ?allocNodes, ?retiredNodes, hpRem, ?initRetired, ?nhazardNodes, true) &*& hpRem != nil;
    ensures validLhp(allClients, allocNodes, retiredNodes, tail(hpRem), initRetired, nhazardNodes, false);
{
    open validLhp(allClients, allocNodes, retiredNodes, hpRem, initRetired, nhazardNodes, true);
    switch(hpRem) { case nil: case cons(h, t): }
    assert length(tail(hpRem)) == length(hpRem) - 1;
    int len = length(allClients) - length(hpRem);
    int newLen = length(allClients) - length(tail(hpRem));
    assert newLen == len + 1;
    append_drop_take(allClients, len);
    assert allClients == append(take(len, allClients), hpRem);
    drop_append(newLen, take(len, allClients), hpRem);
    close validLhp(allClients, allocNodes, retiredNodes, tail(hpRem), initRetired, nhazardNodes, false);
}        
                
lemma void foreach_validLhp_helper_cons_allocated(list<hpRec> l, list<struct stack_client*> allClients, list<struct node*> allocated, list<struct node*> retired, struct node* n, struct stack_client *c)
    requires foreach(l, validLhp_helper(allClients, allocated, retired)) &*& !mem(n, retired);
    ensures foreach(l, validLhp_helper(cons(c, allClients), cons(n, allocated), retired));
{
    switch(l) {
        case nil:
            open foreach(l, validLhp_helper(allClients, allocated, retired));
            close foreach(l, validLhp_helper(cons(c, allClients), cons(n, allocated), retired));
        case cons(h, t):
            open foreach(l, validLhp_helper(allClients, allocated, retired));
            foreach_validLhp_helper_cons_allocated(t, allClients, allocated, retired, n, c);
            open validLhp_helper(allClients, allocated, retired)(h);
            validLhp_cons_alloc(allClients, allocated, retired, n, c);
            close validLhp_helper(cons(c, allClients), cons(n, allocated), retired)(h);
            close foreach(l, validLhp_helper(cons(c, allClients), cons(n, allocated), retired));
            
    }
}
lemma void foreach_validLhp_helper_replace_allocated(list<hpRec> l, list<struct stack_client*> allClients, list<struct node*> alloc1, list<struct node*> alloc2, list<struct node*> retired, struct node* n1, struct node* n2)
    requires foreach(l, validLhp_helper(allClients, append(alloc1, cons(n1, alloc2)), retired)) &*& !mem(n2, retired);
    ensures foreach(l, validLhp_helper(allClients, append(alloc1, cons(n2, alloc2)), retired));
{
    switch(l) {
        case nil:
            open foreach(l, validLhp_helper(allClients, append(alloc1, cons(n1, alloc2)), retired));
            close foreach(l, validLhp_helper(allClients, append(alloc1, cons(n2, alloc2)), retired));
        case cons(h, t):
            open foreach(l, validLhp_helper(allClients, append(alloc1, cons(n1, alloc2)), retired));
            foreach_validLhp_helper_replace_allocated(t, allClients, alloc1, alloc2, retired, n1, n2);
            open validLhp_helper(allClients, append(alloc1, cons(n1, alloc2)), retired)(h);
            validLhp_replace_alloc(allClients, alloc1, n1, n2, alloc2, retired);
            close validLhp_helper(allClients, append(alloc1, cons(n2, alloc2)), retired)(h);
            close foreach(l, validLhp_helper(allClients, append(alloc1, cons(n2, alloc2)), retired));
            
    }
}
lemma void foreach_validLhp_helper_insert_retired(list<hpRec> l, list<struct stack_client*> allClients, list<struct node*> alloc, list<struct node*> retired1, list<struct node*> retired2, struct node* n)
    requires foreach(l, validLhp_helper(allClients, alloc, append(retired1, retired2)));
    ensures foreach(l, validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2))));
{
    switch(l) {
        case nil:
            open foreach(l, validLhp_helper(allClients, alloc, append(retired1, retired2)));
            close foreach(l, validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2))));
        case cons(h, t):
            open foreach(l, validLhp_helper(allClients, alloc, append(retired1, retired2)));
            foreach_validLhp_helper_insert_retired(t, allClients, alloc, retired1, retired2, n);
            open validLhp_helper(allClients, alloc, append(retired1, retired2))(h);
            validLhp_insert_retired(allClients, alloc, retired1, n, retired2);
            close validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2)))(h);
            close foreach(l, validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2))));
            
    }
}


lemma void validLhp_remove_retired(list<struct node*> retired1, struct node* n, list<struct node*> retired2, list<struct node*> lhpValid1, list<struct node*> lhpValid2)
    requires validLhp(?allClients, ?allocNodes, append(retired1, cons(n, retired2)), nil, append(lhpValid1, cons(n, lhpValid2)), ?hpNodes, false) &*& 
        !mem(n, retired1) &*& !mem(n, retired2) &*& !mem(n, lhpValid1) &*& !mem(n, lhpValid2);
    ensures validLhp(allClients, allocNodes, append(retired1, retired2), nil, append(lhpValid1, lhpValid2), hpNodes, false);
{
    open validLhp(allClients, allocNodes, append(retired1, cons(n, retired2)), nil, append(lhpValid1, cons(n, lhpValid2)), hpNodes, false);
    mem_append((struct node*)0, lhpValid1, cons(n, lhpValid2));
    mem_append((struct node*)0, lhpValid1, lhpValid2);
    
    if(!lset_subset(append(lhpValid1, lhpValid2), append(retired1, retired2))) {
        lset_subset_contains_conv(append(lhpValid1, lhpValid2), append(retired1, retired2));
        open exwitness(?x);
        lset_union_contains(lhpValid1, lhpValid2, x);
        lset_union_contains(retired1, retired2, x);
        lset_subset_contains(append(lhpValid1, cons(n, lhpValid2)), append(retired1, cons(n, retired2)), x);
        lset_union_contains(lhpValid1, cons(n, lhpValid2), x);
        lset_union_contains(retired1, cons(n, retired2), x);
        assert false;
    }
    list<struct node*> newLhpValid = append(lhpValid1, lhpValid2);
    list<struct node*> lhpValid = append(lhpValid1, cons(n, lhpValid2));
    if(!lset_subset(lset_inters(allocNodes, newLhpValid), lset_inters(hpNodes, newLhpValid))) {
        lset_subset_contains_conv(lset_inters(allocNodes, newLhpValid), lset_inters(hpNodes, newLhpValid));
        open exwitness(?x);
        lset_inters_contains(allocNodes, newLhpValid, x);
        lset_inters_contains(hpNodes, newLhpValid, x);
        lset_subset_contains(lset_inters(allocNodes, lhpValid), lset_inters(hpNodes, lhpValid), x);
        lset_inters_contains(allocNodes, lhpValid, x);
        lset_inters_contains(hpNodes, lhpValid, x);
        lset_union_contains(lhpValid1, lhpValid2, x);
        lset_union_contains(lhpValid1, cons(n, lhpValid2), x);
        assert false;
    }
    close validLhp(allClients, allocNodes, append(retired1, retired2), nil, append(lhpValid1, lhpValid2), hpNodes, false);
}

lemma void foreach_validLhp_helper_remove_retired(list<hpRec> l, list<struct stack_client*> allClients, list<struct node*> alloc, list<struct node*> retired1, struct node* n, list<struct node*> retired2)
    requires foreach(l, validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2)))) &*& !containsValidNode(l, n) &*& !mem(n, retired1) &*& !mem(n, retired2);
    ensures foreach(l, validLhp_helper(allClients, alloc, append(retired1, retired2)));
{
    switch(l) {
        case nil:
            open foreach(l, validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2))));
            close foreach(l, validLhp_helper(allClients, alloc, append(retired1, retired2)));
        case cons(h, t):
            open foreach(l, validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2))));
            foreach_validLhp_helper_remove_retired(t, allClients, alloc, retired1, n, retired2);
            open validLhp_helper(allClients, alloc, append(retired1, cons(n, retired2)))(h);
            open validLhp(allClients, alloc, append(retired1, cons(n, retired2)), ?lhpRem, ?lhpValid, ?lhpNodes, ?fcc);
            
            assert !mem(n, lhpValid);
            list<struct node*> retiredNodes = append(retired1, cons(n, retired2));
            list<struct node*> newRetiredNodes = append(retired1, retired2);
            
            if(!lset_subset(lhpValid, newRetiredNodes)) {
                lset_subset_contains_conv(lhpValid, newRetiredNodes);
                open exwitness(?x);
                lset_subset_contains(lhpValid, retiredNodes, x);
                lset_union_contains(retired1, retired2, x);
                lset_union_contains(retired1, cons(n,retired2), x);
                assert false;
            }
            
            close validLhp(allClients, alloc, append(retired1, retired2), lhpRem, lhpValid, lhpNodes, fcc);
            close validLhp_helper(allClients, alloc, append(retired1, retired2))(h);
            close foreach(l, validLhp_helper(allClients, alloc, append(retired1, retired2)));
            
    }

}
lemma void validLhp_rearrange_retired(list<struct stack_client*> allClients, list<struct node*> alloc, list<struct node*> retired1, list<struct node*> retired2)
    requires validLhp(allClients, alloc, retired1, ?hpRem, ?hpValid, ?hpList, ?fcc) &*& lset_equals(retired1, retired2) == true;
    ensures validLhp(allClients, alloc, retired2, hpRem, hpValid, hpList, fcc);
{
    open validLhp(allClients, alloc, retired1, hpRem, hpValid, hpList, fcc);
    if(!lset_subset(hpValid, retired2)) {
        lset_subset_contains_conv(hpValid, retired2);
        open exwitness(?x);
        lset_subset_contains(hpValid, retired1, x);
        lset_equals_contains(retired1, retired2, x);
        assert false;
    }
    close validLhp(allClients, alloc, retired2, hpRem, hpValid, hpList, fcc);
}

lemma void foreach_validLhp_helper_rearrange_retired(list<hpRec> l, list<struct stack_client*> allClients, list<struct node*> alloc, list<struct node*> retired1, list<struct node*> retired2)
    requires foreach(l, validLhp_helper(allClients, alloc, retired1)) &*& lset_equals(retired1, retired2) == true;
    ensures foreach(l, validLhp_helper(allClients, alloc, retired2));
{
    switch(l) {
        case nil:
            open foreach(l, validLhp_helper(allClients, alloc, retired1));
            close foreach(l, validLhp_helper(allClients, alloc, retired2));
        case cons(h, t):
            open foreach(l, validLhp_helper(allClients, alloc, retired1));
            foreach_validLhp_helper_rearrange_retired(t, allClients, alloc, retired1, retired2);
            open validLhp_helper(allClients, alloc, retired1)(h);
            validLhp_rearrange_retired(allClients, alloc, retired1, retired2);
            close validLhp_helper(allClients, alloc, retired2)(h);
            close foreach(l, validLhp_helper(allClients, alloc, retired2));
    }

}

lemma void full_stack_client_retired(struct stack_client* head) 
    requires clients(head, 0, ?allClientsId, ?stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists) &*& 
        stack->full_fraction_helper |-> _ ;
    ensures clients(head, 0, allClientsId, stack, allClients, allocNodes, poppedNodes, retiredNodes, hpLists) &*& 
        stack->full_fraction_helper |-> _  &*&
        lset_remove(allocNodes, 0) == nil &*& poppedNodes == nil &*& hpLists == nil;
{
    open clients(head, 0, allClientsId, stack, allClients, allocNodes, poppedNodes, retiredNodes, hpLists);
    if(head != 0) {
        open stack_client_internal(head, allClientsId, stack, _, ?next, _, _, _, _, _, _, _, ?active);
        full_stack_client_retired(next);
        close stack_client_internal(head, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
    }
    close clients(head, 0, allClientsId, stack, allClients, allocNodes, poppedNodes, retiredNodes, hpLists);
}        
    
@*/

struct stack *create_stack()
    //@ requires true;
    //@ ensures stack_free(result);
{
    struct stack *s = malloc(sizeof(struct stack));
    if (s == 0) abort();
    s->head = 0;
    s->clients = 0;
    s->hpCount = 0;
    //@ close lseg(0, 0, nil, nil);
    //@ close foreach(nil, node_tracker_helper(nil, 1));
    //@ close foreach(nil, node_tracker_helper(nil, 0));
    //@ close foreach(nil, node_tracker_helper(nil, 0));
    //@ close foreach(nil, validLhp_helper(nil, nil, nil));
    //@ int allClientsId = create_ghost_list();
    //@ s->allClientsId = allClientsId;
    //@ close clients(0, 0, allClientsId, s, nil, nil, nil, nil, nil);
    //@ close stackInternal(s, nil, allClientsId);
    //@ close stack_ctor(s, allClientsId)();
    //@ create_atomic_space(stack_ctor(s, allClientsId));
    //@ close stack_helper(s, allClientsId);
    //@ close stack_free(s);
    return s;
}



void dispose_stack(struct stack *stack)
    //@ requires stack_free(stack);
    //@ ensures true;
{
    //@ open stack_free(stack);
    //@ open stack_helper(stack, ?allClientsId);
    //@ dispose_atomic_space(stack_ctor(stack, allClientsId));
    //@ open stack_ctor(stack, allClientsId)();
    //@ open stackInternal(stack, ?elems, allClientsId);
    
    //@ assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);

    //@ full_stack_client_retired(ch);
    
    //@ open foreach(poppedNodes, node_tracker_helper(allocNodes, 0));
    //@ open foreach(hpLists, validLhp_helper(allClients, allocNodes, retiredNodes));
    
    struct stack_client* client = stack->clients;
    while(client != 0) 
    /*@ invariant stack->full_fraction_helper |-> _ &*& 
            clients(client, 0, allClientsId, stack, ?remClients, ?remAllocNodes, nil, ?remRetiredNodes, nil) &*& 
            lset_remove(allocNodes, 0) == nil &*&
            foreach(remRetiredNodes, node_tracker_helper(allocNodes, 0)) &*&
            !mem((struct node*)0, remRetiredNodes);
    @*/
    {
        //@ open clients(client, 0, allClientsId, stack, remClients, remAllocNodes, nil, remRetiredNodes, nil);
        //@ open stack_client_internal(client, _, stack, _, _, _, _, ?retired, _, _, _, _, _);
        struct stack_client* next = client->next;
        //@ assert client->active == (void*)0; 
        //@ assert clients(next, 0, allClientsId, stack, ?remClients0, ?remAllocNodes0, nil, ?remRetired0, nil);
        struct linkedlist* rlist = client->rlist;
        //@ assert linkedlist(rlist, retired);
        //@ foreach_split(retired, remRetired0);
        //@ mem_append((struct node*)0, retired, remRetired0);
        while(!linkedlist_is_empty(rlist)) 
        /*@ invariant linkedlist(rlist, ?nretired) &*& foreach(nretired, node_tracker_helper(allocNodes, 0)) &*& 
                lset_remove(allocNodes, 0) == nil &*& !mem((struct node*)0, nretired);
        @*/
        {
            struct node* n = linkedlist_pop(rlist);
            //@ open foreach(nretired, node_tracker_helper(allocNodes, 0));
            //@ open node_tracker_helper(allocNodes, 0)(n);
            //@ lset_remove_contains(allocNodes, 0, n);
            //@ assert (n != 0);
            //@ occ_mem(allocNodes, n);
            //@ open node_tracker(n, ?id, 0);
            //@ destroy_cptracker(id);
            //@ open node_cp_helper(n, _);
            free(n);
        }
        //@ assert nretired == nil;
        //@ open foreach(nretired, node_tracker_helper(allocNodes, 0));
        linkedlist_dispose(rlist); 
        free(client);
        client = next;
    }
    //@ open clients(client, 0, allClientsId, stack, _, _, _, _, _);
    //@ open foreach(remRetiredNodes, node_tracker_helper(allocNodes, 0));
    
    struct node* node = stack->head;
    while(node != 0) 
    /*@ invariant 
            lseg(node, 0, ?nodes, _) &*& 
            foreach(nodes, node_tracker_helper(allocNodes, 1)) &*&
            lset_remove(allocNodes, 0) == nil;
    @*/
    {
        //@ open lseg(node, 0, nodes, _);
        //@ open tracked_node_fraction(node, _, _, ?f);
        struct node* next = node->next;
        //@ close [f] node_cp_helper(node, _);
        //@ assert lseg(next, 0, ?nodes0, ?elems0);
        //@ open foreach(nodes, node_tracker_helper(allocNodes, 1));
        //@ open node_tracker_helper(allocNodes, 1)(node);
        //@ lset_remove_contains(allocNodes, 0, node);
        //@ occ_mem(allocNodes, node);
        //@ open node_tracker(node, ?id, 1);
        //@ cptracker_match(id);
        //@ assert cpticket(id, ?tid, _);
        //@ destroy_cpticket(id, tid);
        //@ destroy_cptracker(id);
        //@ open node_cp_helper(node, _);
        free(node);
        node = next;
    }
    //@ open lseg(node, 0, _, _);
    //@ open foreach(nodes, node_tracker_helper(allocNodes, 1));
    
    free(stack);
    
    //@ leak ghost_list(allClientsId, _);
}

void increment_hpCount(struct stack *stack)
    //@ requires [?f]stack_helper(stack, ?allClientsId);
    //@ ensures [f]stack_helper(stack, allClientsId);
{
    //TODO: maybe exchange the full_fraction_helper for a contribution to the hpCounter
    //      int this case, the spec's of this method may change
    bool succeeded = false;
    while(!succeeded) 
        //@ invariant [f]stack_helper(stack, allClientsId);
    {
        //@ open [f]stack_helper(stack, allClientsId);
        int oldHpCount;
        //@ int oldHpCountProphecy = create_prophecy_int();
        {
            /*@
            predicate_family_instance atomic_load_int_context_pre(context)(predicate() inv, int *pp, int prophecy) =
                inv == stack_ctor(stack, allClientsId) &*&
                pp == &stack->hpCount &*& 
                prophecy == oldHpCountProphecy;
            predicate_family_instance atomic_load_int_context_post(context)() = 
                true;
            lemma void context(atomic_load_int_operation *op) : atomic_load_int_context
                requires
                    atomic_load_int_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                    is_atomic_load_int_operation(op) &*& atomic_load_int_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_int_context_post(context)() &*& inv() &*&
                    is_atomic_load_int_operation(op) &*& atomic_load_int_operation_post(op)();
            {
                open atomic_load_int_context_pre(context)(inv, pp, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                op();
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_load_int_context_post(context)();
            }
            @*/
            //@ close atomic_load_int_context_pre(context)(stack_ctor(stack, allClientsId), &stack->hpCount, oldHpCountProphecy);
            //@ produce_lemma_function_pointer_chunk(context);
            oldHpCount = atomic_load_int(&stack->hpCount);
            //@ open atomic_load_int_context_post(context)();
            //@ leak is_atomic_load_int_context(context);
        }
        if(oldHpCount > INT_MAX - 1) abort();
        int oldHpCountCasResult;
        //@ int oldHpCountCasResultProphecy = create_prophecy_int();
        {
            /*@
            predicate_family_instance atomic_compare_and_store_int_context_pre(context)(predicate() inv, int *pp, int old, int new, int prophecy) = 
                inv == stack_ctor(stack, allClientsId) &*& 
                pp == &stack->hpCount &*& 
                old == oldHpCount &*& 
                new == oldHpCount + 1 &*& 
                prophecy == oldHpCountCasResultProphecy &*& //end of argument fixing
                true;
            predicate_family_instance atomic_compare_and_store_int_context_post(context)() = 
                true;
            lemma void context(atomic_compare_and_store_int_operation *op):atomic_compare_and_store_int_context
                requires
                    atomic_compare_and_store_int_context_pre(context)(?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
                    is_atomic_compare_and_store_int_operation(op) &*&
                    atomic_compare_and_store_int_operation_pre(op)(pp, old, new, prophecy);
                ensures
                    atomic_compare_and_store_int_context_post(context)() &*& inv() &*&
                    is_atomic_compare_and_store_int_operation(op) &*&
                    atomic_compare_and_store_int_operation_post(op)();
            {
                open atomic_compare_and_store_int_context_pre(context)(inv, pp, old, new, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                op();
                close stackInternal(stack, _, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_compare_and_store_int_context_post(context)();
            }
            @*/
            //@ close atomic_compare_and_store_int_context_pre(context)(stack_ctor(stack, allClientsId), &stack->hpCount, oldHpCount, oldHpCount + 1, oldHpCountCasResultProphecy);
            //@ produce_lemma_function_pointer_chunk(context);
            oldHpCountCasResult = atomic_compare_and_store_int(&stack->hpCount, oldHpCount, oldHpCount + 1);
            //@ open atomic_compare_and_store_int_context_post(context)();
            //@ leak is_atomic_compare_and_store_int_context(context);
        }
        //@ close [f]stack_helper(stack, allClientsId);
    }
    
}


struct stack_client* get_first_stack_client(struct stack *stack)
//@ requires [?f]stack_helper(stack, ?allClientsId);
//@ ensures [f]stack_helper(stack, allClientsId) &*& (result != 0 ? [_]ghost_list_member_handle(allClientsId, result) : true);
{
    //@ open [f] stack_helper(stack, allClientsId);
    struct stack_client *sc = 0;
    //@ struct stack_client *schProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
            inv == stack_ctor(stack, allClientsId) &*&
            pp == &stack->clients &*& 
            prophecy == schProphecy;
        predicate_family_instance atomic_load_pointer_context_post(context)() = 
            schProphecy != 0 ? [_]ghost_list_member_handle(allClientsId, schProphecy) : true ;
        lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(context)() &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
        {
            open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            op();
            open clients(ch, 0, allClientsId, stack, _, _, _, _, _);
            if(ch != 0) {
                open stack_client_internal(ch, _, _, _, _, _, _, _, _, _, _, _, ?active);
                close stack_client_internal(ch, _, _, _, _, _, _, _, _, _, _, _, active);
            }
            close clients(ch, 0, allClientsId, stack, _, _, _, _, _);
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_load_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->clients, schProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        sc = atomic_load_pointer(&stack->clients);
        //@ open atomic_load_pointer_context_post(context)();
        //@ leak is_atomic_load_pointer_context(context);
    }
    //@ close [f] stack_helper(stack, allClientsId);
    return sc;
}

struct stack_client* get_next_stack_client(struct stack *stack, struct stack_client* client)
//@ requires [?f]stack_helper(stack, ?allClientsId) &*& [_]ghost_list_member_handle(allClientsId, client) &*& client != 0;
//@ ensures [f]stack_helper(stack, allClientsId) &*& (result != 0 ? [_]ghost_list_member_handle(allClientsId, result) : true);
{
    //@ open [f]stack_helper(stack, allClientsId);
    struct stack_client *sc = client;
    //@ struct stack_client *scProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
            inv == stack_ctor(stack, allClientsId) &*&
            pp == &sc->next &*& 
            prophecy == scProphecy &*&
            sc != 0 &*&
            [_]ghost_list_member_handle(allClientsId, sc);
        predicate_family_instance atomic_load_pointer_context_post(context)() = 
            (scProphecy == 0 ? true : [_]ghost_list_member_handle(allClientsId, scProphecy));
        lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(context)() &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
        {
            open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                
            ghost_list_member_handle_lemma();
            clients_split(ch, sc);
            open clients(sc, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(sc, _, _, _, ?scn, _, _, _, _, _, _, _, ?active);
            op();
            assert scn == scProphecy;
            open clients(scn, 0, allClientsId, stack, _, _, _, _, _);
            if(scn != 0) {
                open stack_client_internal(scn, _, _, _, _, _, _, _, _, _, _, _, ?active2);
                close stack_client_internal(scn, _, _, _, _, _, _, _, _, _, _, _, active2);
            }
            close clients(scn, 0, allClientsId, stack, _, _, _, _, _);
            close stack_client_internal(sc, _, _, _, _, _, _, _, _, _, _, _, active);
            close clients(sc, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
               
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_load_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &sc->next, scProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        sc = atomic_load_pointer(&sc->next);
        //@ open atomic_load_pointer_context_post(context)();
        //@ leak is_atomic_load_pointer_context(context);
    }
    //@ close [f]stack_helper(stack, allClientsId);
    return sc;
}

bool try_insert_new_stack_client(struct stack *stack, struct stack_client* sc)
//@ requires [?f]stack_helper(stack, ?allClientsId) &*& stack_client_precursor(sc, stack, 0, false, _, 0, f);
//@ ensures [f]stack_helper(stack, allClientsId) &*& (result ? stack_client(sc, allClientsId, stack, 0, false, 0, f) : stack_client_precursor(sc, stack, 0, false, _, 0, f));
{
    struct stack_client *sch = get_first_stack_client(stack);
        
    //@ open stack_client_precursor(sc, stack, 0, false, _, 0, f); 
    sc->next = sch;
    //@ close stack_client_precursor(sc, stack, 0, false, sch, 0, f); 
        
    //@ open [f] stack_helper(stack, allClientsId);
    struct stack_client * casResult = 0;
    //@ struct stack_client *casResultProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv, void **pp, void *old, void *new, void *prophecy) = 
            inv == stack_ctor(stack, allClientsId) &*& pp == &stack->clients &*& old == sch &*& new == sc &*& prophecy == casResultProphecy &*& //end of argument fixing
            stack_client_precursor(sc, stack, 0, false, sch, 0, f); 
        predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() = 
            casResultProphecy == sch ? stack_client(sc, allClientsId, stack, 0, false, 0, f) : stack_client_precursor(sc, stack, 0, false, sch, 0, f); 
        lemma void context(atomic_compare_and_store_pointer_operation *op):atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(context)(?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
            ensures
                atomic_compare_and_store_pointer_context_post(context)() &*& inv() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_post(op)();
        {
            open atomic_compare_and_store_pointer_context_pre(context)(inv, pp, old, new, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            op();
            if(prophecy == sch) {
                assert stack->head |-> ?head &*& lseg(head, 0, ?nodes, elems);
                assert clients(sch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists) &*& ghost_list(allClientsId, allClients);
                open stack_client_precursor(sc, stack, 0, false, sch, 0, f);
                ghost_list_insert(allClientsId, nil, allClients, sc);
                leak ghost_list_member_handle(allClientsId, sc);
                close stack_client_internal(sc, allClientsId, stack, 0, sch, false, 0, _, _, _, _, _, true);
                close clients(sc, 0, allClientsId, stack, cons(sc, allClients), _, _, _, _);
                close stack_client_int(sc, allClientsId, stack, 0, false, 0, ?retired, false, nil, nil, false, f);
                close stack_client(sc, allClientsId, stack, 0, false, 0, f);
                updateAllocNodes_helper3(nodes, allocNodes, 1, 0);
                updateAllocNodes_helper3(retiredNodes, allocNodes, 0, 0);
                updateAllocNodes_helper3(poppedNodes, allocNodes, 0, 0);
                foreach_validLhp_helper_cons_allocated(hpLists, allClients, allocNodes, retiredNodes, 0, sc);
            }
            close stackInternal(stack, _, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_compare_and_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_compare_and_store_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->clients, sch, sc, casResultProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        casResult = atomic_compare_and_store_pointer(&stack->clients, sch, sc);
        //@ open atomic_compare_and_store_pointer_context_post(context)();
        //@ leak is_atomic_compare_and_store_pointer_context(context);
    }
    return (casResult == sch);
    //@ close [f] stack_helper(stack, allClientsId);
}

bool try_acquire_stack_client(struct stack *stack, struct stack_client* client)
/*@ requires [?f]stack_helper(stack, ?allClientsId) &*&
        [f]stack->full_fraction_helper |-> _ &*&
        client != 0 &*&
        [_]ghost_list_member_handle(allClientsId, client);
@*/
/*@ ensures [f]stack_helper(stack, allClientsId) &*&
        [_]ghost_list_member_handle(allClientsId, client) &*&
        (result ? 
            stack_client(client, allClientsId, stack, 0, false, 0, f)
            :
            [f]stack->full_fraction_helper |-> _
        );
@*/
{
    //@ open [f] stack_helper(stack, allClientsId); 

    void *casResult = 0;
    //@ void *casResultProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv, void **pp, void *old, void *new, void *prophecy) = 
            inv == stack_ctor(stack, allClientsId) &*& 
            pp == &client->active &*& 
            old == (void*)0 &*& 
            new == (void*)1 &*& 
            prophecy == casResultProphecy &*& //end of argument fixing
            [_]ghost_list_member_handle(allClientsId, client) &*&
            [f]stack->full_fraction_helper |-> _;
        predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() = 
            [_]ghost_list_member_handle(allClientsId, client) &*&
            casResultProphecy == (void*)0 ? 
                stack_client(client, allClientsId, stack, 0, false, 0, f) : 
                [f]stack->full_fraction_helper |-> _; 
        lemma void context(atomic_compare_and_store_pointer_operation *op):atomic_compare_and_store_pointer_context
            requires
                atomic_compare_and_store_pointer_context_pre(context)(?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
            ensures
                atomic_compare_and_store_pointer_context_post(context)() &*& inv() &*&
                is_atomic_compare_and_store_pointer_operation(op) &*&
                atomic_compare_and_store_pointer_operation_post(op)();
        {
            open atomic_compare_and_store_pointer_context_pre(context)(inv, pp, old, new, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            ghost_list_member_handle_lemma();
            clients_split(ch, client);
            open clients(client, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(client, _, _, _, _, _, _, _, _, _, _, _, ?active);
            op();
            if(casResultProphecy == (void*) 0) {
                client->stack_full_fraction_helper_fraction = f;
                close stack_client_int(client, allClientsId, stack, 0, false, 0, _, false, nil, nil, false, f);
                close stack_client(client, allClientsId, stack, 0, false, 0, f);
            }
            close stack_client_internal(client, _, _, _, _, _, _, _, _, _, _, _, true);
            close clients(client, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
               
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_compare_and_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_compare_and_store_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &client->active, (void*)0, (void*)1, casResultProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        casResult = atomic_compare_and_store_pointer(&client->active, (void*)0, (void*)1);
        //@ open atomic_compare_and_store_pointer_context_post(context)();
        //@ leak is_atomic_compare_and_store_pointer_context(context);
    }

    //@ close [f]stack_helper(stack, allClientsId); 
    
    return casResult == (void*)0;
}

struct stack_client* stack_create_client(struct stack *stack)
    //@ requires [?f]stack_free(stack);
    //@ ensures stack_with_client(stack, result, f); 
{
    //@ open [f]stack_free(stack);
    //@ assert [f]stack_helper(stack, ?allClientsId);
    struct stack_client *sc = get_first_stack_client(stack);
    bool acquired = false;
    while(sc != 0 && !acquired)
    /*@ invariant [f]stack_helper(stack, allClientsId) &*& 
            (sc != 0 ? [_]ghost_list_member_handle(allClientsId, sc) : true) &*&
            (acquired ? stack_client(sc, allClientsId, stack, 0, false, 0, f) : [f]stack->full_fraction_helper |-> _ );
    @*/
    {
        acquired = try_acquire_stack_client(stack, sc);
        if(!acquired)
            sc = get_next_stack_client(stack, sc);
    }
    if(!acquired) {
        increment_hpCount(stack);
    
        bool succeeded = false;
    
        sc = malloc(sizeof(struct stack_client));
        if (sc == 0) abort();
        sc->hp = 0;
        sc->active = (void*)1;
        struct linkedlist* rlist = linkedlist_create();
        sc->rlist = rlist;
        //@ sc->hpAllocated = false;
        //@ sc->stack = stack;
        //@ sc->popped = 0;
        //@ sc->localHpList = nil;
        //@ sc->retiredNodes = nil;
        //@ sc->localHpActive = false;
        //@ sc->localHpRemClients = nil;
        //@ sc->localHpFirstCollected = false;
        //@ sc->stack_full_fraction_helper_fraction = f;
        //@ close stack_client_precursor(sc, stack, 0, false, _, 0, f);
        while(!succeeded) 
        //@ invariant [f] stack_helper(stack, allClientsId) &*& succeeded ? stack_client(sc, allClientsId, stack, 0, false, 0, f) : stack_client_precursor(sc, stack, 0, false, _, 0, f);
        {
            succeeded = try_insert_new_stack_client(stack, sc);
        }
    }
    //@ close stack_with_client(stack, sc, f);
    return sc;
}

void stack_dispose_client(struct stack *stack, struct stack_client* client)
   //@ requires stack_with_client(stack, client, ?f); 
   //@ ensures [f]stack_free(stack); 
{
    //@ open stack_with_client(stack, client, f);
    //@ open [f] stack_helper(stack, ?allClientsId); 
    
    {
        /*@
        predicate_family_instance atomic_store_pointer_context_pre(context)(predicate() inv, void **pp, void *value) =
            inv == stack_ctor(stack, allClientsId) &*&
            pp == &client->active &*& 
            value == 0 &*& 
            stack_client(client, allClientsId, stack, 0, false, 0, f);
        predicate_family_instance atomic_store_pointer_context_post(context)() = 
            [f] stack->full_fraction_helper |-> _;
        lemma void context(atomic_store_pointer_operation *op) : atomic_store_pointer_context
            requires
                atomic_store_pointer_context_pre(context)(?inv, ?pp, ?value) &*& inv() &*&
                is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_pre(op)(pp, value);
            ensures
                atomic_store_pointer_context_post(context)() &*& inv() &*&
                is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_post(op)();
        {
            open atomic_store_pointer_context_pre(context)(inv, pp, value);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            
            open stack_client(client, allClientsId, stack, _, _, _, f);
            open stack_client_int(client, allClientsId, stack, _, _, _, _, _, _, _, _, f);
            ghost_list_member_handle_lemma();
            clients_split(ch, client);
            open clients(client, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(client, allClientsId, stack, _, ?clnext, _, _, _, _, _, _, _, _);
            op();
            close stack_client_internal(client, allClientsId, stack, _, clnext, _, _, _, _, _, _, _, false);
            close clients(client, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_store_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &client->active, (void*)0);
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_store_pointer(&client->active, (void*)0);
        //@ open atomic_store_pointer_context_post(context)();
        //@ leak is_atomic_store_pointer_context(context);
    }
    //@ close [f]stack_helper(stack, allClientsId); 
    //@ close [f]stack_free(stack);
}

void stack_push(struct stack *stack, struct stack_client *client, void *data)
    //@ requires stack_with_client(stack, client, ?f);
    //@ ensures stack_with_client(stack, client, f);
{
    //@ open stack_with_client(stack, client, f);
    //@ assert [f] stack_helper(stack, ?allClientsId) &*& stack_client(client, allClientsId, stack, _, _, _, f); 
    
    struct node *node = malloc(sizeof(struct node));
    if (node == 0) abort();
    node->data = data;
    node->next = 0;
    //@ close node_precursor(node, 0, data, _);
    bool succeeded = false;
    while(!succeeded) 
    /*@
    invariant [f] stack_helper(stack, allClientsId) &*& 
        (succeeded ? true : node_precursor(node, _, data, _));
    @*/
    {
        //@ open [f]stack_helper(stack, allClientsId);
        struct node *h = 0;
        //@ struct node *hProphecy = create_prophecy_pointer();
        {
            /*@
            predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
                inv == stack_ctor(stack, allClientsId) &*&
                pp == &stack->head &*& 
                prophecy == hProphecy;
            predicate_family_instance atomic_load_pointer_context_post(context)() = 
                true;
            lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_pointer_context_post(context)() &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
            {
                open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                op();
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_load_pointer_context_post(context)();
            }
            @*/
            //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->head, hProphecy);
            //@ produce_lemma_function_pointer_chunk(context);
            h = atomic_load_pointer(&stack->head);
            //@ open atomic_load_pointer_context_post(context)();
            //@ leak is_atomic_load_pointer_context(context);
        }
        //@ open node_precursor(node, _, data, _);
        node->next = h;
        //@ close node_precursor(node, h, data, _);
        
        struct node *casResult;
        //@ struct node *casResultProphecy = create_prophecy_pointer();
        {
            /*@
            predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv, void **pp, void *old, void *new, void *prophecy) = 
                inv == stack_ctor(stack, allClientsId) &*& pp == &stack->head &*& old == h &*& new == node &*& prophecy == casResultProphecy &*& //end of argument fixing
                node_precursor(node, h, data, _); 
            predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() = 
                casResultProphecy == h ? true : node_precursor(node, h, data, _); 
            lemma void context(atomic_compare_and_store_pointer_operation *op):atomic_compare_and_store_pointer_context
                requires
                    atomic_compare_and_store_pointer_context_pre(context)(?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
                    is_atomic_compare_and_store_pointer_operation(op) &*&
                    atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
                ensures
                    atomic_compare_and_store_pointer_context_post(context)() &*& inv() &*&
                    is_atomic_compare_and_store_pointer_operation(op) &*&
                    atomic_compare_and_store_pointer_operation_post(op)();
            {
                open atomic_compare_and_store_pointer_context_pre(context)(inv, pp, old, new, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                struct node* head = stack->head;
                op();
                if(prophecy == h) {
                    assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, _, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                    assert lseg(head, 0, ?nodes, elems);
                    
                    node_precursor_lseg_distinct(node, nodes);
                    node_precursor_foreach_node_tracker_helper_distinct(node, poppedNodes, allocNodes, 0);
                    node_precursor_foreach_node_tracker_helper_distinct(node, retiredNodes, allocNodes, 0);
                    
                    int trackerId = create_cptracker_precursor(node_cp_helper, node);
                    open node_precursor(node, h, data, _);
                    open node(node, h, data, _);
                    node->trackerId = trackerId;
                    close node(node, h, data, trackerId);
                    close node_cp_helper(node, _);
                    convert_cptracker_precursor(trackerId);
                    create_cpticket(trackerId);
                    open [?f2] node_cp_helper(node, _);
                    close tracked_node_fraction(node, h, data, f2);
                    list<struct node*> newNodes = cons(node, nodes);
                    close lseg(node, 0, newNodes, cons(data, elems)); 
                    close node_tracker(node, trackerId, 1);

                    lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), node);
                    lset_remove_contains(allocNodes, 0, node); 
                    lset_union_contains(nodes, lset_union(poppedNodes, retiredNodes), node);
                    lset_union_contains(poppedNodes, retiredNodes, node);
                    occ_mem(allocNodes, node);
                    assert occ(allocNodes, node) == 0; 
                    
                    close node_tracker_helper(allocNodes, 1)(node);
                    close foreach(newNodes, node_tracker_helper(allocNodes, 1));
                    
                    if(!lset_subset(lset_remove(allocNodes, 0), lset_union(newNodes, lset_union(poppedNodes, retiredNodes)))) {
                        lset_subset_contains_conv(lset_remove(allocNodes, 0), lset_union(newNodes, lset_union(poppedNodes, retiredNodes)));
                        open exwitness(?x);
                        lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), x);
                        assert false;
                    }
                }
                close stackInternal(stack, _, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_compare_and_store_pointer_context_post(context)();
            }
            @*/
            //@ close atomic_compare_and_store_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->head, h, node, casResultProphecy);
            //@ produce_lemma_function_pointer_chunk(context);
            casResult = atomic_compare_and_store_pointer(&stack->head, h, node);
            //@ open atomic_compare_and_store_pointer_context_post(context)();
            //@ leak is_atomic_compare_and_store_pointer_context(context);
        }
        succeeded = (casResult == h);
        //@ close [f]stack_helper(stack, allClientsId);
    }
    //@ close stack_with_client(stack, client, f);
}

/*@
lemma void deallocate_hazard_pointer(struct node* h, list<struct node*> allocNodes1, list<struct node*> allocNodes2, list<struct stack_client*> allClients)
    requires 
        tracked_node_fraction(h, _, _, _) &*&
        foreach(?nodes, node_tracker_helper(append(allocNodes1, cons(h, allocNodes2)), 1)) &*&
        foreach(?retiredNodes, node_tracker_helper(append(allocNodes1, cons(h, allocNodes2)), 0)) &*&
        foreach(?poppedNodes, node_tracker_helper(append(allocNodes1, cons(h, allocNodes2)), 0)) &*&
        foreach(?hpLists, validLhp_helper(allClients, append(allocNodes1, cons(h, allocNodes2)), retiredNodes)) &*&
        !mem<struct node*>(0, nodes) &*&
        !mem<struct node*>(0, retiredNodes) &*&
        !mem<struct node*>(0, poppedNodes) &*&
        distinct(nodes) == true &*&
        distinct(poppedNodes) == true &*&
        distinct(retiredNodes) == true &*&
        lset_disjoint(nodes, retiredNodes) == true &*&
        lset_disjoint(nodes, poppedNodes) == true &*&
        lset_disjoint(poppedNodes, retiredNodes) == true &*&
        lset_subset(lset_remove(append(allocNodes1, cons(h, allocNodes2)), 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes))) == true;
    ensures 
        foreach(nodes, node_tracker_helper(append(allocNodes1, cons((struct node*)0, allocNodes2)), 1)) &*&
        foreach(retiredNodes, node_tracker_helper(append(allocNodes1, cons((struct node*)0, allocNodes2)), 0)) &*&
        foreach(poppedNodes, node_tracker_helper(append(allocNodes1, cons((struct node*)0, allocNodes2)), 0)) &*&
        foreach(hpLists, validLhp_helper(allClients, append(allocNodes1, cons((struct node*)0, allocNodes2)), retiredNodes)) &*&
        lset_subset(lset_remove(append(allocNodes1, cons((struct node*)0, allocNodes2)), 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes))) == true;    
{
    open tracked_node_fraction(h, _, _, ?fh); 
    open [fh]node(h, _, _, _);
    assert h != 0;
    close [fh]node(h, _, _, _);
    close tracked_node_fraction(h, _, _, fh);
   
    list<struct node*> allocNodes = append(allocNodes1, cons(h, allocNodes2));
    list<struct node*> newAllocNodes = append(allocNodes1, cons((struct node*)0, allocNodes2));
    occ_append(allocNodes1, cons((struct node*)0, allocNodes2), h);
    occ_append(allocNodes1, cons(h, allocNodes2), h);
    assert occ(newAllocNodes, h) == occ(allocNodes, h) - 1;
   
    lset_union_contains(allocNodes1, cons(h, allocNodes2), h);
    assert lset_contains(allocNodes, h) == true;
    lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), h);
    lset_remove_contains(allocNodes, 0, h);
    lset_union_contains(nodes, lset_union(poppedNodes, retiredNodes), h);
    lset_union_contains(poppedNodes, retiredNodes, h);
    assert lset_contains(nodes, h)|| lset_contains(poppedNodes, h) || lset_contains(retiredNodes, h);

    //release tracked_node_fraction and update foreaches
    list<struct node *> container;
    int containerExtra = 0;
    list<struct node *> other1;
    int extra1 = 0;
    list<struct node *> other2;
    int extra2 = 0;
    if(lset_contains(nodes, h)) {
        container = nodes;
        containerExtra = 1;
        other1 = poppedNodes;
        other2 = retiredNodes;
    } else {
        extra1 = 1;
        other1 = nodes;
        if(lset_contains(poppedNodes, h)) {
            container = poppedNodes;
            other2 = retiredNodes;
        } else {
            container = retiredNodes;
            other2 = poppedNodes;
        }
    }
    lset_inters_contains(nodes, retiredNodes, h);
    lset_inters_contains(nodes, poppedNodes, h);
    lset_inters_contains(poppedNodes, retiredNodes, h);
    
    foreach_remove_helper(h, container, node_tracker_helper(allocNodes, containerExtra));
    open node_tracker_helper(allocNodes, containerExtra)(h);
    open node_tracker(h, ?id, ?count);
    open tracked_node_fraction(h, _, _, ?f3);
    close [f3]node_cp_helper(h, _);
    cptracker_match(id);
    assert cpticket(id, ?tid, _);
    destroy_cpticket(id, tid);
    close node_tracker(h, id, count-1);
    close node_tracker_helper(newAllocNodes, containerExtra)(h);
    distinct_mem_remove(h, container);
    remove_nomem((struct node*)0, h, container);
    updateAllocNodes_helper4(remove(h, container), allocNodes1, allocNodes2, containerExtra, h, 0);
    foreach_unremove_helper(h, container, node_tracker_helper(newAllocNodes, containerExtra));
    
    updateAllocNodes_helper4(other1, allocNodes1, allocNodes2, extra1, h, 0);
    updateAllocNodes_helper4(other2, allocNodes1, allocNodes2, extra2, h, 0);
    
    foreach_validLhp_helper_replace_allocated(hpLists, allClients, allocNodes1, allocNodes2, retiredNodes, h, 0);

    if(!lset_subset(lset_remove(newAllocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)))) {
        lset_subset_contains_conv(lset_remove(newAllocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)));
        open exwitness(?x);
        lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), x);
        lset_remove_contains(newAllocNodes, 0, x);
        lset_remove_contains(allocNodes, 0, x);
        lset_union_contains(allocNodes1, cons((struct node*) 0, allocNodes2), x);
        lset_union_contains(allocNodes1, cons(h, allocNodes2), x);
        assert false;
    }
}

@*/

//TODO: need multiple methods for hazard pointer setting
// set_validated_hazard_pointer (pass a lemma's to separate and unseparate the node_fraction_tracker from the atomic space) 
// set_hazard_pointer and read_and_validate_hazard_pointer

/* @

predicate stackInternal_ds(struct stack *stack, list<struct node*> nodes, list<void *> elems) =
    malloc_block_stack(stack) &*&
    stack->head |-> ?head &*& 
    lseg(head, 0, nodes, elems);
    
predicate stackInternal_hps(struct stack *stack, int allClientsId, list<struct node*> nodes) =
    stack->clients |-> ?clients &*&
    [1/2]stack->allClientsId |-> allClientsId &*& 
    clients(clients, 0, allClientsId, stack, ?clientsList, ?allocNodes, ?poppedNodes, ?retiredNodes, ?lhpRs) &*& 
    ghost_list<struct stack_client*>(allClientsId, clientsList) &*&
    stack->hpCount |-> ?hpCount &*& hpCount >= 0 &*& //TODO: hpCount >= length(allocNodes) &*&
    foreach(nodes, node_tracker_helper(allocNodes, 1)) &*&
    foreach(retiredNodes, node_tracker_helper(allocNodes, 0)) &*&
    foreach(poppedNodes, node_tracker_helper(allocNodes, 0)) &*&
    foreach(lhpRs, validLhp_helper(clientsList, allocNodes, retiredNodes)) &*&
    !mem<struct node*>(0, nodes) &*&
    !mem<struct node*>(0, retiredNodes) &*&
    !mem<struct node*>(0, poppedNodes) &*&
    distinct(nodes) == true &*&
    distinct(poppedNodes) == true &*&
    distinct(retiredNodes) == true &*&
    lset_disjoint(nodes, retiredNodes) == true &*&
    lset_disjoint(nodes, poppedNodes) == true &*&
    lset_disjoint(poppedNodes, retiredNodes) == true &*&
    lset_subset(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes))) == true;

lemma void open_stack2(struct stack* stack)
    requires stackInternal(stack, ?elems, ?allClientsId);
    ensures stackInternal_ds(stack, ?nodes, elems) &*& stackInternal_hps(stack, allClientsId, nodes);
{
    open stackInternal(stack, elems, allClientsId);
    close stackInternal_ds(stack, _, elems);
    close stackInternal_hps(stack, allClientsId, _, _);
}
lemma void close_stack2(struct stack* stack)
    requires stackInternal_ds(stack, ?nodes, ?elems) &*& stackInternal_hps(stack, ?allClientsId, nodes);
    ensures stackInternal(stack, elems, allClientsId);
{
    open stackInternal_ds(stack, _, elems);
    open stackInternal_hps(stack, allClientsId, _, _);
    close stackInternal(stack, elems, allClientsId);
}    
predicate_family validate_hazard_pointer_helper_lemma_pre(void *lem)(struct stack* stack, struct stack_client *client, struct node* h);
predicate_family validate_hazard_pointer_helper_lemma_post(void *lem)(struct stack* stack, struct stack_client *client, struct node* h);

typedef lemma void validate_hazard_pointer_helper_lemma(struct stack* stack, struct stack_client *client, struct node* h);
    requires stackInternal_ds(stack, ?nodes, ?elems) &*& stackInternal_hps(stack, ?allClientsId, nodes) &*&
        stack_client(client, allClientsId, stack, h, false, ?popped, ?f) &*& 
        h != 0 &*&
        validate_hazard_pointer_helper_lemma_pre(this)(stack, client, h);
    ensures stackInternal_ds(stack, nodes, elems) &*& stackInternal_hps(stack, allClientsId, nodes) &*&
        stack_client(client, allClientsId, stack, h, false, popped, f) &*&
        mem(h, nodes) == true &*&
        validate_hazard_pointer_helper_lemma_post(this)(stack, client, h);
@* /

void validate_hazard_pointer_lemma(struct stack *stack, struct stack_client *client, struct node* h)
/*@ requires [?f] stack_helper(stack, ?allClientsId) &*&
        stack_client(client, allClientsId, stack, h, false, ?popped, f) &*&
        h != 0  &*&
        is_validate_hazard_pointer_helper_lemma(?lem) &*&
        validate_hazard_pointer_helper_lemma_pre(lem)(stack, client, h);
@* /
/*@ ensures [f] stack_helper(stack, allClientsId) &*&
        stack_client(client, allClientsId, stack, h, true, popped, f) &*&
        tracked_node_fraction(h, _, _, _) &*&
        is_validate_hazard_pointer_helper_lemma(lem) &*&
        validate_hazard_pointer_helper_lemma_post(lem)(stack, client, h);
@* /
{
    //@ open [f]stack_helper(stack, allClientsId);
    {
        /*@
            predicate_family_instance atomic_noop_context_pre(context)(predicate() inv) = 
                inv == stack_ctor(stack, allClientsId) &*&
                stack_client(client, allClientsId, stack, h, false, popped, f) &*&
                h != 0  &*&
                is_validate_hazard_pointer_helper_lemma(lem) &*&
                validate_hazard_pointer_helper_lemma_pre(lem)(stack, client, h);
            predicate_family_instance atomic_noop_context_post(context)() = 
                stack_client(client, allClientsId, stack, h, true, popped, f) &*&
                tracked_node_fraction(h, _, _, _) &*&
                is_validate_hazard_pointer_helper_lemma(lem) &*&
                validate_hazard_pointer_helper_lemma_post(lem)(stack, client, h);
            lemma void context(): atomic_noop_context
                requires atomic_noop_context_pre(context)(?inv) &*& inv();
                ensures atomic_noop_context_post(context)() &*& inv();
            {
                open atomic_noop_context_pre(context)(inv);
                open stack_ctor(stack, allClientsId)();
                open_stack2(stack);
                lem(stack, client, h);
                
                
                close_stack2(stack);
                close stack_ctor(stack, allClientsId)();
                close atomic_noop_context_post(context)();
            }
        @* /
        //@ close atomic_noop_context_pre(context)(stack_ctor(stack, allClientsId));
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_noop();
        //@ open atomic_noop_context_post(context)();
        //@ leak is_atomic_noop_context(context);
    }
    //@ close [f]stack_helper(stack, allClientsId);
}
*/

bool try_validate_hazard_pointer(struct stack *stack, struct stack_client *client, struct node* h)
/*@ requires [?f] stack_helper(stack, ?allClientsId) &*&
        stack_client(client, allClientsId, stack, h, false, ?popped, f) &*&
        h != 0;
@*/
/*@ ensures [f] stack_helper(stack, allClientsId) &*&
        stack_client(client, allClientsId, stack, h, result, popped, f) &*&
        (result ? tracked_node_fraction(h, _, _, _) : true);
@*/
{
    //@ open [f]stack_helper(stack, allClientsId);
    struct node *hAgain = 0;
    //@ struct node *hAgainProphecy = create_prophecy_pointer();
    {
        //between reading stack->head and storing client->hp, other threads may pop the node, retire it and free it.
        //therefore, we need to read stack->head again and ensure that it is still (or again) h
        //this guarantees that h has not been freed, and therefore it is possible to acquire a fraction of the node
        /*@
            predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
                inv == stack_ctor(stack, allClientsId) &*&
                pp == &stack->head &*& 
                prophecy == hAgainProphecy &*&
                stack_client(client, allClientsId, stack, h, false, popped, f) &*&
                h != 0;
            predicate_family_instance atomic_load_pointer_context_post(context)() = 
                stack_client(client, allClientsId, stack, h, hAgainProphecy == h, popped, f) &*&
                (hAgainProphecy == h ? tracked_node_fraction(h, _, _, _) : true);
            lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_pointer_context_post(context)() &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
            {
                open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                op();
                if(hAgainProphecy == h) {
                    assert stack->head |-> ?sh &*& lseg(sh, 0, ?nodes, elems);
                    assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                        
                    open stack_client(client, allClientsId, stack, h, false, popped, f);
                    open stack_client_int(client, allClientsId, stack, h, false, popped, _, _, _, _, false, f);
                    ghost_list_member_handle_lemma();
                    clients_split(ch, client);
                    open clients(client, 0, allClientsId, stack, _, _, _, _, _);
                    open stack_client_internal(client, allClientsId, stack, _, ?cn, _, _, _, _, _, _, _, ?active);
                    assert clients(ch, client, allClientsId, stack, _, ?allocNodes1, ?poppedNodes1, ?retiredNodes1, ?hpLists1);
                    assert clients(cn, 0, allClientsId, stack, _, ?allocNodes2, ?poppedNodes2, ?retiredNodes2, ?hpLists2);
                    client->hpAllocated = true;
                    close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
                    close clients(client, 0, allClientsId, stack, _, _, _, _, _);
                    clients_join(ch);
                    list<struct node*> newAllocNodes = append(allocNodes1, cons(h, allocNodes2));
                    assert clients(ch, 0, allClientsId, stack, _, newAllocNodes, poppedNodes, retiredNodes, hpLists);
                    close stack_client_int(client, allClientsId, stack, h, true, popped, _, _, _, _, false, f);
                    close stack_client(client, allClientsId, stack, h, true, popped, f);

                    open lseg(h, 0, nodes, elems);
                    assert tracked_node_fraction(h, ?hn, _, _);
                    assert lseg(hn, 0, ?nodes0, _);
                    close lseg(h, 0, cons(h, nodes0), elems);
                        
                        
                    open foreach(nodes, node_tracker_helper(allocNodes, 1));
                    open node_tracker_helper(allocNodes, 1)(h);
                    open node_tracker(h, ?id, ?count);
                    assert count == occ(allocNodes, h) + 1;
                    int tid = create_cpticket(id);
                    open [?f2]node_cp_helper(h, _);
                    close tracked_node_fraction(h, _, _, f2);
                    close node_tracker(h, id, count + 1);

                    occ_append(allocNodes1, cons((struct node*)0, allocNodes2), h);
                    occ_append(allocNodes1, cons(h, allocNodes2), h);
                    assert occ(newAllocNodes, h) == occ(allocNodes, h) + 1;
                    close node_tracker_helper(newAllocNodes, 1)(h);
                    updateAllocNodes_helper4(nodes0, allocNodes1, allocNodes2, 1, 0, h);
                        
                    close foreach(nodes, node_tracker_helper(newAllocNodes, 1));
                        
                    updateAllocNodes_helper4(retiredNodes, allocNodes1, allocNodes2, 0, 0, h);
                    updateAllocNodes_helper4(poppedNodes, allocNodes1, allocNodes2, 0, 0, h);
                       
                    foreach_validLhp_helper_replace_allocated(hpLists, allClients, allocNodes1, allocNodes2, retiredNodes, 0, h);
                     
                    if(!lset_subset(lset_remove(newAllocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)))) {
                        lset_subset_contains_conv(lset_remove(newAllocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)));
                        open exwitness(?x);
                        lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), x);
                        lset_remove_contains(newAllocNodes, 0, x);
                        lset_remove_contains(allocNodes, 0, x);
                        lset_union_contains(allocNodes1, cons((struct node*)0, allocNodes2), x);
                        lset_union_contains(allocNodes1, cons(h, allocNodes2), x);
                        assert false;
                    }
                        
                }
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_load_pointer_context_post(context)();
            }
            @*/
        //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->head, hAgainProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        hAgain = atomic_load_pointer(&stack->head);
       //@ open atomic_load_pointer_context_post(context)();
       //@ leak is_atomic_load_pointer_context(context);
    }
    //@ close [f] stack_helper(stack, allClientsId);
    return h == hAgain;
}

void set_hazard_pointer(struct stack *stack, struct stack_client *client, struct node* h)
/*@ requires [?f] stack_helper(stack, ?allClientsId) &*&
        stack_client(client, allClientsId, stack, ?prev, ?alloc, ?popped, f) &*&
        ( alloc ? tracked_node_fraction(prev, _, _, _) : true );
@*/
/*@ ensures [f] stack_helper(stack, allClientsId) &*&
        stack_client(client, allClientsId, stack, h, false, popped, f);
@*/
{
    //@ open [f] stack_helper(stack, allClientsId);
    {
    /*@
        predicate_family_instance atomic_store_pointer_context_pre(context)(predicate() inv, void **pp, void *value) =
            inv == stack_ctor(stack, allClientsId) &*&
            pp == &client->hp &*& 
            value == h &*& 
            stack_client(client, allClientsId, stack, prev, alloc, popped, f) &*&
            ( alloc ? tracked_node_fraction(prev, _, _, _) : true );
        predicate_family_instance atomic_store_pointer_context_post(context)() = 
            stack_client(client, allClientsId, stack, h, false, popped, f);
        lemma void context(atomic_store_pointer_operation *op) : atomic_store_pointer_context
            requires
                atomic_store_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_store_pointer_context_post(context)() &*& inv() &*&
                is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_post(op)();
        {
            open atomic_store_pointer_context_pre(context)(inv, pp, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            open stack_client(client, allClientsId, stack, prev, alloc, popped, f);
            open stack_client_int(client, allClientsId, stack, prev, alloc, popped, ?retired, false, nil, nil, false, f);
            ghost_list_member_handle_lemma();
            clients_split(ch, client);
            open clients(client, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(client, allClientsId, stack, _, ?clnext, _, _, _, _, _, _, _, ?active);
            assert clients(ch, client, allClientsId, stack, _, ?allocNodes1, _, _, _);
            assert clients(clnext, 0, allClientsId, stack, _, ?allocNodes2, _, _, _);
            op();
            client->hpAllocated = false;
            close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
            close clients(client, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
            close stack_client_int(client, allClientsId, stack, h, false, popped, _, _, _, _, false, f);
            close stack_client(client, allClientsId, stack, h, false, popped, f);
            
            if(alloc) {
                //deallocate prev
                deallocate_hazard_pointer(prev, allocNodes1, allocNodes2, allClients);
            }
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_store_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &client->hp, h);
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_store_pointer(&client->hp, h);
        //@ open atomic_store_pointer_context_post(context)();
        //@ leak is_atomic_store_pointer_context(context);
    }
    //@ close [f] stack_helper(stack, allClientsId);
}

void reset_hazard_pointer(struct stack *stack, struct stack_client *client)
//@ requires [?f] stack_helper(stack, ?allClientsId) &*& stack_client(client, allClientsId, stack, ?h, ?alloc, ?popped, f) &*& (alloc ? tracked_node_fraction(h, _, _, _) : true);
//@ ensures [f] stack_helper(stack, allClientsId) &*& stack_client(client, allClientsId, stack, 0, false, popped, f);
{
    set_hazard_pointer(stack, client, 0);
}

void *stack_try_pop(struct stack *stack, struct stack_client *client)
    //@ requires stack_with_client(stack, client, ?f);
    //@ ensures stack_with_client(stack, client, f);
{
    //@ open stack_with_client(stack, client, f);
    //@ assert [f] stack_helper(stack, ?allClientsId) &*& stack_client(client, allClientsId, stack, _, _, _, f); 
    bool succeeded = false;
    void* result = 0;
    struct node *h;
    while (!succeeded) 
    // @ invariant [f]stack_helper(stack, allClientsId) &*& (succeeded ? stack_client(client, allClientsId, stack, 0, false, h, f) : stack_client(client, allClientsId, stack, 0, false, 0, f));
    /*@ invariant [f]stack_helper(stack, allClientsId) &*& 
            stack_client(client, allClientsId, stack, ?hazP, ?hpAlloc, ?poppedNode, f) &*&
            (succeeded ? poppedNode == h : poppedNode == 0) &*&
            (hpAlloc ? tracked_node_fraction(hazP, _, _, _) : true);
    @*/
    {
        //@ open [f]stack_helper(stack, allClientsId);
        
        //@ struct node *hProphecy = create_prophecy_pointer();
        {
            /*@
            predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
                inv == stack_ctor(stack, allClientsId) &*&
                pp == &stack->head &*& 
                prophecy == hProphecy;
            predicate_family_instance atomic_load_pointer_context_post(context)() = 
                true;
            lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_pointer_context_post(context)() &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
            {
                open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                op();
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_load_pointer_context_post(context)();
            }
            @*/
            //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->head, hProphecy);
            //@ produce_lemma_function_pointer_chunk(context);
            h = atomic_load_pointer(&stack->head);
            //@ open atomic_load_pointer_context_post(context)();
            //@ leak is_atomic_load_pointer_context(context);
        }
        //@ close [f]stack_helper(stack, allClientsId);
        if(h == 0) {
            result = 0;
            succeeded = true;
        } else {
            set_hazard_pointer(stack, client, h);
            
            bool validated = try_validate_hazard_pointer(stack, client, h);
            
            if(validated) {
                //@ assert stack_client(client, allClientsId, stack, h, true, 0, f) &*& tracked_node_fraction(h, _, _, _);

                //@ open tracked_node_fraction(h, _, _, ?f2);
                //@ open [f2]node(h, _, _, _);
                struct node *next = h->next;
                result = h->data;
                //@ close [f2]node(h, next, result, _);
                //@ close tracked_node_fraction(h, next, result, f2);
                
                //@ open [f]stack_helper(stack, allClientsId);
                //@ assert stack_client(client, allClientsId, stack, h, true, 0, f) &*& tracked_node_fraction(h, next, result, _);
                struct node *casResult; 
                //@ struct node *casResultProphecy = create_prophecy_pointer();
                {
                    /*@
                    predicate_family_instance atomic_compare_and_store_pointer_context_pre(context)(predicate() inv, void **pp, void *old, void *new, void *prophecy) = 
                        inv == stack_ctor(stack, allClientsId) &*& pp == &stack->head &*& old == h &*& new == next &*& prophecy == casResultProphecy &*& //end of argument fixing
                        tracked_node_fraction(h, next, result, _) &*& 
                        stack_client(client, allClientsId, stack, h, true, 0, f);
                    predicate_family_instance atomic_compare_and_store_pointer_context_post(context)() = 
                        tracked_node_fraction(h, next, result, _) &*& 
                        casResultProphecy == h ? 
                            stack_client(client, allClientsId, stack, h, true, h, f): 
                            stack_client(client, allClientsId, stack, h, true, 0, f);
                    lemma void context(atomic_compare_and_store_pointer_operation *op):atomic_compare_and_store_pointer_context
                        requires
                            atomic_compare_and_store_pointer_context_pre(context)(?inv, ?pp, ?old, ?new, ?prophecy) &*& inv() &*&
                            is_atomic_compare_and_store_pointer_operation(op) &*&
                            atomic_compare_and_store_pointer_operation_pre(op)(pp, old, new, prophecy);
                        ensures
                            atomic_compare_and_store_pointer_context_post(context)() &*& inv() &*&
                            is_atomic_compare_and_store_pointer_operation(op) &*&
                            atomic_compare_and_store_pointer_operation_post(op)();
                    {
                        open atomic_compare_and_store_pointer_context_pre(context)(inv, pp, old, new, prophecy);
                        open stack_ctor(stack, allClientsId)();
                        open stackInternal(stack, _, allClientsId);
                        struct node* head = stack->head;

                        assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);

                        op();
                            
                        if(casResultProphecy == h) {
                            //at this moment, h is still the head of the stack
                            assert head == h;
                            
                            //open up lseg and prove that the next is still the same
                            open tracked_node_fraction(h, next, result, ?f3);
                            assert h != 0;
                            open [f3]node(h, next, result, _);
                            open lseg(head, 0, ?nodes, ?elems);
                            open tracked_node_fraction(head, _, _, ?f4);
                            open [f4]node(head, _, _, _);
                            close [f3]node(h, next, result, _);
                            close [f4]node(head, next, result, _);
                            assert lseg(next, 0, ?nodes0, _);
                            close tracked_node_fraction(head, next, result, f3);
                            close tracked_node_fraction(head, next, result, f4);
                            
                            //remove the tracker from the foreach
                            open foreach(nodes, node_tracker_helper(allocNodes, 1));
                            assert node_tracker_helper(allocNodes, 1)(h);
                            
                            //deallocate the fraction from the lseg
                            open node_tracker_helper(allocNodes, 1)(h);
                            open node_tracker(h, ?id, ?count);
                            open tracked_node_fraction(head, next, result, f4);
                            close [f4]node_cp_helper(head, _);
                            cptracker_match(id);
                            assert cpticket(id, ?tid, f4);
                            destroy_cpticket(id, tid);
                            close node_tracker(h, id, count - 1);
                            close node_tracker_helper(allocNodes, 0)(h);
                            
                            //update the stack_client
                            open stack_client(client, allClientsId, stack, h, true, 0, f);
                            open stack_client_int(client, allClientsId, stack, h, true, 0, _, _, _, _, false, f);
                            ghost_list_member_handle_lemma();
                            clients_split(ch, client);
                            open clients(client, 0, allClientsId, stack, _, _, _, _, _);
                            open stack_client_internal(client, allClientsId, stack, ?hp, ?clnext, ?alloc, ?popped, ?retired, ?hpList, _, _, _, ?active);
                            close stack_client_internal(client, allClientsId, stack, h, clnext, true, popped, retired, hpList, _, _, _, active);
                            assert clients(ch, client, allClientsId, stack, _, ?allocNodes1, ?poppedNodes1, ?retiredNodes1, ?hpLists1) &*& clients(clnext, 0, allClientsId, stack, _, ?allocNodes2, ?poppedNodes2, ?retiredNodes2, ?hpLists2);
                            open stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
                            client->popped = h;
                            close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
                            close clients(client, 0, allClientsId, stack, _, _, _, _, _);
                            clients_join(ch);
                            list<struct node*> newPoppedNodes = append(poppedNodes1, cons(h, poppedNodes2));
                            assert clients(ch, 0, allClientsId, stack, _, allocNodes, newPoppedNodes, retiredNodes, hpLists);
                            close stack_client_int(client, allClientsId, stack, h, true, h, _, _, _, _, false, f);
                            close stack_client(client, allClientsId, stack, h, true, h, f);
                            
                            //add the tracker to the foreach of poppedNodes
                            foreach_split(poppedNodes1, poppedNodes2);
                            close foreach(cons(h, poppedNodes2), node_tracker_helper(allocNodes, 0));
                            foreach_append(poppedNodes1, cons(h, poppedNodes2));
                            assert foreach(newPoppedNodes, node_tracker_helper(allocNodes, 0));
                            
                            //prove pure properties
                            mem_append((struct node*)0, poppedNodes1, poppedNodes2);
                            mem_append((struct node*)0, poppedNodes1, cons(h, poppedNodes2));
                            assert !mem((struct node*)0, newPoppedNodes);
                            assert !mem(h, poppedNodes);
                            distinct_insert(poppedNodes1, poppedNodes2, h);
                            assert distinct(newPoppedNodes)==true;
                            
                            switch(lset_inters(nodes0, newPoppedNodes)) {
                                case nil:
                                case cons(x, t):
                                    lset_inters_contains(nodes0, newPoppedNodes, x);
                                    lset_inters_contains(nodes0, poppedNodes, x);
                                    lset_union_contains(poppedNodes1, poppedNodes2, x);
                                    lset_union_contains(poppedNodes1, cons(h, poppedNodes2), x);
                                    assert false;
                            }
                            assert lset_disjoint(nodes0, newPoppedNodes) == true;
                            
                            switch(lset_inters(newPoppedNodes, retiredNodes)) {
                                case nil:
                                case cons(x, t):
                                    lset_inters_contains(newPoppedNodes, retiredNodes, x);
                                    lset_inters_contains(poppedNodes, retiredNodes, x);
                                    lset_union_contains(poppedNodes1, poppedNodes2, x);
                                    lset_union_contains(poppedNodes1, cons(h, poppedNodes2), x);
                                    assert false;
                            }
                            assert lset_disjoint(newPoppedNodes, retiredNodes) == true;
                            
                            if(!lset_subset(lset_remove(allocNodes, 0), lset_union(nodes0, lset_union(newPoppedNodes, retiredNodes)))) {
                                lset_subset_contains_conv(lset_remove(allocNodes, 0), lset_union(nodes0, lset_union(newPoppedNodes, retiredNodes)));
                                open exwitness(?x);
                                lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), x);
                                lset_union_contains(nodes, lset_union(poppedNodes, retiredNodes), x);
                                lset_union_contains(poppedNodes, retiredNodes, x);
                                lset_union_contains(nodes0, lset_union(newPoppedNodes, retiredNodes), x);
                                lset_union_contains(newPoppedNodes, retiredNodes, x);
                                lset_union_contains(poppedNodes1, poppedNodes2, x);
                                lset_union_contains(poppedNodes1, cons(h, poppedNodes2), x);
                                assert false;
                            }
                        } 
                        close stackInternal(stack, _, allClientsId);
                        close stack_ctor(stack, allClientsId)();
                        close atomic_compare_and_store_pointer_context_post(context)();
                    }
                    @*/
                    //@ close atomic_compare_and_store_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->head, h, next, casResultProphecy);
                    //@ produce_lemma_function_pointer_chunk(context);
                    casResult = atomic_compare_and_store_pointer(&stack->head, h, next);
                    //@ open atomic_compare_and_store_pointer_context_post(context)();
                    //@ leak is_atomic_compare_and_store_pointer_context(context);
                }
                //@ close [f]stack_helper(stack, allClientsId);
                succeeded = (casResult == h);
            } else {
                //head node was popped before the allocation of the hazard pointer was completed
            }
        }
    }
    
    // @ close [f]stack_helper(stack, allClientsId);
    reset_hazard_pointer(stack, client);
    // @ open [f]stack_helper(stack, allClientsId);
    
    if(h != 0) {
        //insert the popped node into the deleted lst
        retire_node(stack, client, h);
    }
    //@ close stack_with_client(stack, client, f);
    return result;
}

int readHpCount(struct stack *stack)
//@ requires [?f]stack_helper(stack, ?allClientsId);
//@ ensures [f]stack_helper(stack, allClientsId) &*& result >= 0;
{
    //@ open [f]stack_helper(stack, allClientsId);
    int oldHpCount;
    //@ int oldHpCountProphecy = create_prophecy_int();
    {
        /*@
        predicate_family_instance atomic_load_int_context_pre(context)(predicate() inv, int *pp, int prophecy) =
            inv == stack_ctor(stack, allClientsId) &*&
            pp == &stack->hpCount &*& 
            prophecy == oldHpCountProphecy;
        predicate_family_instance atomic_load_int_context_post(context)() = 
            oldHpCountProphecy >= 0;
        lemma void context(atomic_load_int_operation *op) : atomic_load_int_context
            requires
                atomic_load_int_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                is_atomic_load_int_operation(op) &*& atomic_load_int_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_int_context_post(context)() &*& inv() &*&
                is_atomic_load_int_operation(op) &*& atomic_load_int_operation_post(op)();
        {
            open atomic_load_int_context_pre(context)(inv, pp, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            op();
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_load_int_context_post(context)();
        }
        @*/
         //@ close atomic_load_int_context_pre(context)(stack_ctor(stack, allClientsId), &stack->hpCount, oldHpCountProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        oldHpCount = atomic_load_int(&stack->hpCount);
        //@ open atomic_load_int_context_post(context)();
        //@ leak is_atomic_load_int_context(context);
    }
    //@ close [f]stack_helper(stack, allClientsId);
    return oldHpCount;
}

int rcount_limit(int hpCount)
//@ requires 0 <= hpCount;
//@ ensures 0 <= result;
{
    //TODO: this limit is not ok, but does not matter for verification
    //if(hpCount > 40000) abort(); //40000 < sqrt(INT_MAX);
    //return hpCount * (1 + hpCount / 16);
    return hpCount;
}
    
void retire_node(struct stack *stack, struct stack_client* client, struct node* h)
//@ requires [?f]stack_helper(stack, ?allClientsId) &*& stack_client(client, allClientsId, stack, 0, false, h, f) &*& h != 0;
//@ ensures [f]stack_helper(stack, allClientsId) &*& stack_client(client, allClientsId, stack, 0, false, 0, f);
{
    //insert the popped node into rlist
    //@ open stack_client(client, allClientsId, stack, 0, false, h, f);
    //@ open stack_client_int(client, allClientsId, stack, 0, false, h, _, _, _, _, false, f);
    struct linkedlist* rlist = client->rlist;
    //@ list<struct node*> retired = client->retiredNodes;
    //@ close stack_client_int(client, allClientsId, stack, 0, false, h, retired, _, _, _, false, f);
    linkedlist_add(rlist, h);
    
    //@ open [f]stack_helper(stack, allClientsId);
    {
        /*@
            predicate_family_instance atomic_noop_context_pre(context)(predicate() inv) = 
                inv == stack_ctor(stack, allClientsId) &*&
                stack_client_int(client, allClientsId, stack, 0, false, h, retired, false, nil, nil, false, f);
            predicate_family_instance atomic_noop_context_post(context)() = 
                stack_client_int(client, allClientsId, stack, 0, false, 0, cons(h, retired), false, nil, nil, false, f);
    
            lemma void context(): atomic_noop_context
                requires atomic_noop_context_pre(context)(?inv) &*& inv();
                ensures atomic_noop_context_post(context)() &*& inv();
            {
                open atomic_noop_context_pre(context)(inv);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                assert stack->head |-> ?head &*& lseg(head, 0, ?nodes, elems);
                assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                open stack_client_int(client, allClientsId, stack, 0, false, h, retired, false, nil, nil, false, f);
                ghost_list_member_handle_lemma();
                clients_split(ch, client);
                open clients(client, 0, allClientsId, stack, _, _, _, _, _);
                open stack_client_internal(client, allClientsId, stack, _, ?cn, _, _, _, _, _, _, _, ?active);
                assert clients(ch, client, allClientsId, stack, ?allClients1, ?allocNodes1, ?poppedNodes1, ?retiredNodes1, ?hpLists1);
                assert clients(cn, 0, allClientsId, stack, ?allClients2, ?allocNodes2, ?poppedNodes2, ?retiredNodes2, ?hpLists2);
                client->popped = 0;
                client->retiredNodes = cons(h, retired);
                close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
                close clients(client, 0, allClientsId, stack, _, _, _, _, _);
                clients_join(ch);
                assert clients(ch, 0, allClientsId, stack, allClients, allocNodes, ?newPoppedNodes, ?newRetiredNodes, hpLists);
                close stack_client_int(client, allClientsId, stack, 0, false, 0, cons(h, retired), false, nil, nil, false, f);
                assert poppedNodes == append(poppedNodes1, cons(h, poppedNodes2));
                assert newPoppedNodes == append(poppedNodes1, poppedNodes2);
                assert newRetiredNodes == append(retiredNodes1, append(cons(h, retired), retiredNodes2));
                assert retiredNodes == append(retiredNodes1, append(retired, retiredNodes2));
                
                //remove tracker from poppedNodes
                foreach_split(poppedNodes1, cons(h, poppedNodes2));
                open foreach(cons(h, poppedNodes2), node_tracker_helper(allocNodes, 0));
                foreach_append(poppedNodes1, poppedNodes2);
                assert foreach(newPoppedNodes, node_tracker_helper(allocNodes, 0));
                
                //add tracker to retiredNodes
                foreach_split(retiredNodes1, append(retired, retiredNodes2));
                close foreach(append(cons(h, retired), retiredNodes2), node_tracker_helper(allocNodes, 0));
                foreach_append(retiredNodes1, append(cons(h, retired), retiredNodes2));
                assert foreach(newRetiredNodes, node_tracker_helper(allocNodes, 0));
                
                foreach_validLhp_helper_insert_retired(hpLists, allClients, allocNodes, retiredNodes1, append(retired, retiredNodes2), h);
                
                //prove pure properties
                mem_append((struct node*)0, retiredNodes1, append(retired, retiredNodes2));
                mem_append((struct node*)0, retiredNodes1, cons(h, append(retired, retiredNodes2)));
                assert !mem((struct node*)0, newRetiredNodes);
                mem_append((struct node*)0, poppedNodes1, poppedNodes2);
                mem_append((struct node*)0, poppedNodes1, cons(h, poppedNodes2));
                assert !mem((struct node*)0, newPoppedNodes);
                
                insert_distinct_mem(poppedNodes1, poppedNodes2, h);
                remove_append(h, poppedNodes1, cons(h, poppedNodes2));
                distinct_remove(h, poppedNodes);

                mem_append(h, poppedNodes1, cons(h, poppedNodes2));
                lset_inters_contains(poppedNodes, retiredNodes, h);
                mem_append(h, retiredNodes1, append(retired, retiredNodes2));
                mem_append(h, retired, retiredNodes2);
                assert !mem(h, retiredNodes);
                distinct_insert(retiredNodes1, append(retired, retiredNodes2), h);
                
                lset_inters_contains(nodes, poppedNodes, h);
                assert !mem(h, nodes);
                
                switch(lset_inters(nodes, newRetiredNodes)) {
                    case cons(x, t):
                        lset_inters_contains(nodes, newRetiredNodes, x);
                        lset_union_contains(retiredNodes1, append(cons(h, retired), retiredNodes2), x);
                        lset_inters_contains(nodes, retiredNodes, x);
                        lset_union_contains(retiredNodes1, append(retired, retiredNodes2), x);
                        assert false;
                    case nil:
                }
                switch(lset_inters(nodes, newPoppedNodes)) {
                    case cons(x, t): 
                        lset_inters_contains(nodes, newPoppedNodes, x);
                        lset_union_contains(poppedNodes1, poppedNodes2, x);
                        lset_inters_contains(nodes, poppedNodes, x);
                        lset_union_contains(poppedNodes1, cons(h, poppedNodes2), x);
                        assert false;
                    case nil:
                }
                switch(lset_inters(newPoppedNodes, newRetiredNodes)) {
                    case cons(x, t): 
                        lset_inters_contains(newPoppedNodes, newRetiredNodes, x);
                        lset_union_contains(poppedNodes1, poppedNodes2, x);
                        lset_union_contains(retiredNodes1, append(cons(h, retired), retiredNodes2), x);
                        lset_inters_contains(poppedNodes, retiredNodes, x);
                        lset_union_contains(poppedNodes1, cons(h, poppedNodes2), x);
                        lset_union_contains(retiredNodes1, append(retired, retiredNodes2), x);
                        assert false;
                    case nil:
                }
                if(!lset_subset(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(newPoppedNodes, newRetiredNodes)))) {
                    lset_subset_contains_conv(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(newPoppedNodes, newRetiredNodes)));
                    open exwitness(?x);
                    lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), x);
                    lset_union_contains(nodes, lset_union(poppedNodes, retiredNodes), x);
                    lset_union_contains(nodes, lset_union(newPoppedNodes, newRetiredNodes), x);
                    lset_union_contains(poppedNodes, retiredNodes, x);
                    lset_union_contains(newPoppedNodes, newRetiredNodes, x);
                    lset_union_contains(poppedNodes1, poppedNodes2, x);
                    lset_union_contains(retiredNodes1, append(cons(h, retired), retiredNodes2), x);
                    lset_union_contains(poppedNodes1, cons(h, poppedNodes2), x);
                    lset_union_contains(retiredNodes1, append(retired, retiredNodes2), x);
                    assert false;
                }
                
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_noop_context_post(context)();
            }
        @*/
        //@ close atomic_noop_context_pre(context)(stack_ctor(stack, allClientsId));
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_noop();
        //@ open atomic_noop_context_post(context)();
        //@ leak is_atomic_noop_context(context);
    }
    //@ close [f]stack_helper(stack, allClientsId);
    int rCount = linkedlist_count(rlist);
    //@ close stack_client(client, allClientsId, stack, 0, false, 0, f);
    int hpCount = readHpCount(stack);
    int rlimit = rcount_limit(hpCount);
    if(rCount > rlimit) 
    {
        scan(stack, client);
    }
}



struct linkedlist* collect_hazard_pointers(struct stack *stack, struct stack_client* client)
//@ requires [?f]stack_helper(stack, ?allClientsId) &*& stack_client_int(client, allClientsId, stack, 0, false, 0, ?initRetired, false, nil, nil, false, f);
//@ ensures [f]stack_helper(stack, allClientsId) &*& stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, nil, ?hpNodes, false, f) &*& linkedlist(result, hpNodes);
{
    struct linkedlist* hpList = linkedlist_create();
    
    //@ open [f] stack_helper(stack, allClientsId);
    struct stack_client *sc = 0;
    //@ struct stack_client *schProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
            inv == stack_ctor(stack, allClientsId) &*&
            pp == &stack->clients &*& 
            prophecy == schProphecy &*&
            stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, false, nil, nil, false, f);
        predicate_family_instance atomic_load_pointer_context_post(context)() = 
            stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, ?rem, nil, false, f) &*&
            schProphecy != 0 &*& 
            rem != nil &*&
            head(rem) == schProphecy &*&
            [_]ghost_list_member_handle(allClientsId, schProphecy);
        lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(context)() &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
        {
            open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            open stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, false, nil, nil, false, f);
            ghost_list_member_handle_lemma();
            clients_split(ch, client);
            open clients(client, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(client, allClientsId, stack, _, ?clnext, _, _, _, _, _, _, _, ?active);
            assert clients(ch, client, allClientsId, stack, _, ?allocNodes1, ?poppedNodes1, ?retiredNodes1, ?hpLists1);
            assert clients(clnext, 0, allClientsId, stack, _, ?allocNodes2, ?poppedNodes2, ?retiredNodes2, ?hpLists2);
            
            client->localHpActive = true;
            client->localHpRemClients = allClients;
            close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
            close clients(client, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
            close stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, allClients, nil, false, f);
            op();
            clients_length(ch, 0);
            open clients(ch, 0, allClientsId, stack, _, allocNodes, poppedNodes, retiredNodes, ?newHpLists);
            assert newHpLists == append(hpLists1, cons( hpRec(allClients, initRetired, nil, false), hpLists2));
            foreach_split(hpLists1, hpLists2);
            
            mem_append((struct node*) 0, retiredNodes1, append(initRetired, retiredNodes2));
            mem_append((struct node*) 0, initRetired, retiredNodes2);
            if(!lset_subset(initRetired, retiredNodes)) {
                lset_subset_contains_conv(initRetired, retiredNodes);
                open exwitness(?x);
                lset_union_contains(retiredNodes1, append(initRetired, retiredNodes2), x);
                lset_union_contains(initRetired, retiredNodes2, x);
                assert false;
            }
            close validLhp(allClients, allocNodes, retiredNodes, allClients, initRetired, nil, false);
            close validLhp_helper(allClients, allocNodes, retiredNodes)(hpRec(allClients, initRetired, nil, false));
            close foreach(cons( hpRec(allClients, initRetired, nil, false), hpLists2), validLhp_helper(allClients, allocNodes, retiredNodes));
            foreach_append(hpLists1, cons( hpRec(allClients, initRetired, nil, false), hpLists2));
            
            open stack_client_internal(ch, allClientsId, stack, _, _, _, _, _, _, _, _, _, ?active2);
            //provide access to member handle
            close stack_client_internal(ch, allClientsId, stack, _, _, _, _, _, _, _, _, _, active2);
            close clients(ch, 0, allClientsId, stack, _, _, _, _, _);
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_load_pointer_context_post(context)();
            
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->clients, schProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        sc = atomic_load_pointer(&stack->clients);
        //@ open atomic_load_pointer_context_post(context)();
        //@ leak is_atomic_load_pointer_context(context);
    }
    while(sc!=0)
    /*@ invariant [f]atomic_space(stack_ctor(stack, allClientsId)) &*& 
            linkedlist(hpList, ?hazardNodes) &*&
            stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, ?hpRem, hazardNodes, false, f) &*& 
            (sc == 0 ? hpRem == nil : hpRem != nil &*& head(hpRem) == sc &*& [_]ghost_list_member_handle(allClientsId, sc));
    @*/
    {
        // @ switch(hpRem) { case nil: case cons(h, t): }
        struct node* hp = 0;
        //@ struct node *hpProphecy = create_prophecy_pointer();
        {
            /*@
            predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
                inv == stack_ctor(stack, allClientsId) &*&
                pp == &sc->hp &*& 
                prophecy == hpProphecy &*&
                hpRem != nil &*&
                head(hpRem) == sc &*&
                stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, hpRem, hazardNodes, false, f) &*&
                [_]ghost_list_member_handle(allClientsId, sc);
            predicate_family_instance atomic_load_pointer_context_post(context)() = 
                stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, hpRem, ?nhazardNodes, true, f) &*&
                nhazardNodes == (hpProphecy == 0 ? hazardNodes : cons(hpProphecy, hazardNodes)) &*&
                [_]ghost_list_member_handle(allClientsId, sc);
            lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_pointer_context_post(context)() &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();    
            {
                open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                //perform read operation
                ghost_list_member_handle_lemma_helper(allClientsId, sc);
                clients_split(ch, sc);
                open clients(sc, 0, allClientsId, stack, _, _, _, _, _);
                open stack_client_internal(sc, allClientsId, stack, _, ?scnext, ?allocated, _, _, _, _, _, _, ?active);
                assert clients(ch, sc, allClientsId, stack, ?allClients1, ?allocNodes1, _, _, _);
                assert clients(scnext, 0, allClientsId, stack, ?allClients2, ?allocNodes2, _, _, _);
                op();
                close stack_client_internal(sc, allClientsId, stack, hpProphecy, scnext, allocated, _, _, _, _, _, _, active);
                struct node* hazP = (allocated ? hpProphecy : 0);
                close clients(sc, 0, allClientsId, stack, cons(sc, allClients2), cons(hazP, allocNodes2), _, _, _);
                clients_length(sc, 0);
                clients_join(ch);
                assert clients(ch, 0, allClientsId, stack, allClients, allocNodes, poppedNodes, retiredNodes, hpLists);
                clients_length(ch, 0);
                assert allocNodes == append(allocNodes1, cons(hazP, allocNodes2));
                assert allClients == append(allClients1, cons(sc, allClients2));
                assert length(allocNodes2) == length(allClients2);
                assert length(allocNodes1) == length(allClients1);
                
                //update hpRec
                open stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, hpRem, hazardNodes, false, f);
                ghost_list_member_handle_lemma_helper(allClientsId, client);
                clients_split(ch, client);
                open clients(client, 0, allClientsId, stack, _, _, _, _, _);
                open stack_client_internal(client, allClientsId, stack, _, ?clnext, _, _, _, _, _, _, _, ?active2);
                assert clients(ch, client, allClientsId, stack, _, _, _, _, ?hpLists1);
                assert clients(clnext, 0, allClientsId, stack, _, _, _, _, ?hpLists2);
                client->localHpFirstCollected = true;
                if(hpProphecy != 0) {
                    client->localHpList = cons(hpProphecy, hazardNodes);
                } 
                close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active2);
                close clients(client, 0, allClientsId, stack, _, _, _, _, _);
                clients_join(ch);
                close stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, hpRem, _, true, f);
                assert clients(ch, 0, allClientsId, stack, allClients, allocNodes, poppedNodes, retiredNodes, ?newHpLists);
                assert hpLists == append(hpLists1, cons(hpRec(hpRem, initRetired, hazardNodes, false), hpLists2));
                assert newHpLists == append(hpLists1, cons(hpRec(hpRem, initRetired, hpProphecy == 0 ? hazardNodes : cons(hpProphecy, hazardNodes), true), hpLists2));
                
                //update foreach
                foreach_split(hpLists1, cons(hpRec(hpRem, initRetired, hazardNodes, false), hpLists2));
                open foreach(cons(hpRec(hpRem, initRetired, hazardNodes, false), hpLists2), validLhp_helper(allClients, allocNodes, retiredNodes));
                open validLhp_helper(allClients, allocNodes, retiredNodes)(hpRec(hpRem, initRetired, hazardNodes, false));
                open validLhp(allClients, allocNodes, retiredNodes, hpRem, initRetired, hazardNodes, false);
                int len = length(allClients) - length(hpRem);
                assert hpRem == drop(len, allClients);
                drop_append(len, allClients1, cons(sc, allClients2));
                append_drop_take(allClients, len);
                switch(hpRem) { case nil: assert false; case cons(h, t): }
                assert allClients == append(take(len, allClients), cons(sc, tail(hpRem)));
                assert allClients == append(allClients1, cons(sc, allClients2));
                
                clients_distinct(ch);
                assert (distinct(allClients)==true);
                
                split_distinct_unique(take(len, allClients), tail(hpRem), allClients1, allClients2, sc);
                assert hpRem == cons(sc, allClients2);
                close validLhp(allClients, allocNodes, retiredNodes, hpRem, initRetired, hazardNodes, false);
                validLhp_process_client(allocNodes1, hazP, allocNodes2, hpProphecy); 
                //close validLhp(allClients, allocNodes, retiredNodes, hpRem, initRetired, hpProphecy == 0 ? hazardNodes : cons(hpProphecy, hazardNodes), true);
                close validLhp_helper(allClients, allocNodes, retiredNodes)(hpRec(hpRem, initRetired, hpProphecy == 0 ? hazardNodes : cons(hpProphecy, hazardNodes), true));
                close foreach(cons(hpRec(hpRem, initRetired, hpProphecy == 0 ? hazardNodes : cons(hpProphecy, hazardNodes), true), hpLists2), validLhp_helper(allClients, allocNodes, retiredNodes));
                foreach_append(hpLists1, cons(hpRec(hpRem, initRetired, hpProphecy == 0 ? hazardNodes : cons(hpProphecy, hazardNodes), true), hpLists2));
                
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_load_pointer_context_post(context)();
            }
            @*/
            //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &sc->hp, hpProphecy);
            //@ produce_lemma_function_pointer_chunk(context);
            hp = atomic_load_pointer(&sc->hp);
            //@ open atomic_load_pointer_context_post(context)();
            //@ leak is_atomic_load_pointer_context(context);
        }
        if(hp!=0) linkedlist_add(hpList, hp);
        //@ struct stack_client *scProphecy = create_prophecy_pointer();
        //@ assert stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, hpRem, ?nhazardNodes, true, f);
        {
            /*@
            predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
                inv == stack_ctor(stack, allClientsId) &*&
                pp == &sc->next &*& 
                prophecy == scProphecy &*&
                hpRem != nil &*&
                head(hpRem) == sc &*&
                stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, hpRem, nhazardNodes, true, f) &*&
                [_]ghost_list_member_handle(allClientsId, sc);
            predicate_family_instance atomic_load_pointer_context_post(context)() = 
                stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, tail(hpRem), nhazardNodes, false, f) &*&
                scProphecy == 0 ? 
                    tail(hpRem) == nil  : 
                    (tail(hpRem) != nil &*& head(tail(hpRem)) == scProphecy &*& [_]ghost_list_member_handle(allClientsId, scProphecy));
            lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
                requires
                    atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
                ensures
                    atomic_load_pointer_context_post(context)() &*& inv() &*&
                    is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();    
            {
                open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                //perform read operation
                ghost_list_member_handle_lemma();
                clients_split(ch, sc);
                open clients(sc, 0, allClientsId, stack, _, _, _, _, _);
                open stack_client_internal(sc, allClientsId, stack, _, _, _, _, _, _, _, _, _, ?active);
                op();
                struct stack_client* next = sc->next;
                assert clients(ch, sc, allClientsId, stack, ?allClients1, _, _, _, _);
                assert clients(next, 0, allClientsId, stack, ?allClients2, _, _, _, _);
                open clients(next, 0, allClientsId, stack, _, _, _, _, _);
                if(next != 0) {
                    //expose member handle
                    open stack_client_internal(next, allClientsId, stack, _, _, _, _, _, _, _, _, _, ?active2);
                    close stack_client_internal(next, allClientsId, stack, _, _, _, _, _, _, _, _, _, active2);
                }
                close clients(next, 0, allClientsId, stack, _, _, _, _, _);
                close stack_client_internal(sc, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
                close clients(sc, 0, allClientsId, stack, _, _, _, _, _);
                clients_join(ch);
                
                //update stack client
                open stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, hpRem, nhazardNodes, true, f);
                ghost_list_member_handle_lemma_helper(allClientsId, client);
                clients_split(ch, client);
                open clients(client, 0, allClientsId, stack, _, _, _, _, _);
                open stack_client_internal(client, allClientsId, stack, _, ?cnext, _, _, _, _, _, _, _, ?active2);
                assert clients(ch, client, allClientsId, stack, _, _, _, _, ?hpLists1);
                assert clients(cnext, 0, allClientsId, stack, _, _, _, _, ?hpLists2);
                client->localHpFirstCollected = false;
                client->localHpRemClients = tail(hpRem);
                close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active2);
                close clients(client, 0, allClientsId, stack, _, _, _, _, _);
                clients_join(ch);
                close stack_client_int(client, allClientsId, stack, 0, false, 0, initRetired, true, tail(hpRem), nhazardNodes, false, f);
                
                //update foreach
                foreach_split(hpLists1, cons(hpRec(hpRem, initRetired, nhazardNodes, true), hpLists2));
                open foreach(cons(hpRec(hpRem, initRetired, nhazardNodes, true), hpLists2), validLhp_helper(allClients, allocNodes, retiredNodes));
                open validLhp_helper(allClients, allocNodes, retiredNodes)(hpRec(hpRem, initRetired, nhazardNodes, true));
                
                open validLhp(allClients, allocNodes, retiredNodes, hpRem, initRetired, nhazardNodes, true);
                int len = length(allClients) - length(hpRem);
                assert hpRem == drop(len, allClients);
                append_drop_take(allClients, len);
                clients_distinct(ch);
                assert distinct(allClients) == true;
                switch(hpRem) { case nil: case cons(h, t): }
                split_distinct_unique(take(len, allClients), tail(hpRem), allClients1, allClients2, sc);
                close validLhp(allClients, allocNodes, retiredNodes, hpRem, initRetired, nhazardNodes, true);
                
                validLhp_next_client(hpRem);
                close validLhp_helper(allClients, allocNodes, retiredNodes)(hpRec(tail(hpRem), initRetired, nhazardNodes, false));
                close foreach(cons(hpRec(tail(hpRem), initRetired, nhazardNodes, false), hpLists2), validLhp_helper(allClients, allocNodes, retiredNodes));
                foreach_append(hpLists1, cons(hpRec(tail(hpRem), initRetired, nhazardNodes, false), hpLists2));
                
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_load_pointer_context_post(context)();
            }
            @*/
            //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &sc->next, scProphecy);
            //@ produce_lemma_function_pointer_chunk(context);
            sc = atomic_load_pointer(&sc->next);
            //@ open atomic_load_pointer_context_post(context)();
            //@ leak is_atomic_load_pointer_context(context);
        }
    }
    //@ close [f]stack_helper(stack, allClientsId);
    return hpList;
}

struct linkedlist* free_retired_nodes(struct stack *stack, struct stack_client* client, struct linkedlist* hpList, struct linkedlist* rlist)
/*@ requires [?f]stack_helper(stack, ?allClientsId) &*& 
        stack_client_int(client, allClientsId, stack, 0, false, 0, ?initRetired, true, nil, ?hpNodes, false, f) &*& 
        linkedlist(hpList, hpNodes) &*&
        linkedlist(rlist, initRetired);
@*/
/*@ ensures [f]stack_helper(stack, allClientsId) &*& 
        stack_client_int(client, allClientsId, stack, 0, false, 0, ?newRetired, true, nil, hpNodes, false, f) &*& 
        linkedlist(hpList, hpNodes) &*&
        linkedlist(result, newRetired) //TODO: add this: &*& lset_subset(newRetired, rlist) == true
        ;
@*/
{
    struct linkedlist* tmplist = linkedlist_create();

    while(!linkedlist_is_empty(rlist)) 
    /*@ invariant [f]stack_helper(stack, allClientsId) &*& 
            stack_client_int(client, allClientsId, stack, 0, false, 0, ?retired, true, nil, hpNodes, false, f) &*& 
            linkedlist(tmplist, ?retained) &*& linkedlist(rlist, ?remaining) &*& retired == append(retained, remaining) &*&
            linkedlist(hpList, hpNodes);
    @*/
    {
        struct node* n = linkedlist_pop(rlist);
        //@ assert linkedlist(rlist, ?nremaining);
        //@ switch(remaining) { case nil: case cons(h, t): } 
        //@ assert remaining == cons(n, nremaining);
        if(linkedlist_contains(hpList, n)) {
            linkedlist_add_end(tmplist, n);
            //@ append_cons_r_snoc_l(retained, n, nremaining);
        } else {
            //@ open [f]stack_helper(stack, allClientsId);
            {
                /*@
                    predicate_family_instance atomic_noop_context_pre(context)(predicate() inv) = 
                        inv == stack_ctor(stack, allClientsId) &*&
                        stack_client_int(client, allClientsId, stack, 0, false, 0, append(retained, cons(n, nremaining)), true, nil, hpNodes, false, f) &*&
                        !mem(n, hpNodes);
                    predicate_family_instance atomic_noop_context_post(context)() = 
                        stack_client_int(client, allClientsId, stack, 0, false, 0, append(retained, nremaining), true, nil, hpNodes, false, f) &*&
                        node(n, _, _, _);
    
                    lemma void context(): atomic_noop_context
                        requires atomic_noop_context_pre(context)(?inv) &*& inv();
                        ensures atomic_noop_context_post(context)() &*& inv();
                    {
                        open atomic_noop_context_pre(context)(inv);
                        open stack_ctor(stack, allClientsId)();
                        open stackInternal(stack, ?elems, allClientsId);
                        assert stack->head |-> ?head &*& lseg(head, 0, ?nodes, elems);
                        assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                        open stack_client_int(client, allClientsId, stack, 0, false, 0, retired, true, nil, hpNodes, false, f);
                        ghost_list_member_handle_lemma();
                        clients_split(ch, client);
                        open clients(client, 0, allClientsId, stack, _, _, _, _, _);
                        open stack_client_internal(client, allClientsId, stack, _, ?cn, _, _, _, _, _, _, _, ?active);
                        assert clients(ch, client, allClientsId, stack, ?allClients1, ?allocNodes1, ?poppedNodes1, ?retiredNodes1, ?hpLists1);
                        assert clients(cn, 0, allClientsId, stack, ?allClients2, ?allocNodes2, ?poppedNodes2, ?retiredNodes2, ?hpLists2);
                        assert retiredNodes == append(retiredNodes1, append(append(retained, cons(n, nremaining)), retiredNodes2));
                        append_assoc(retained, cons(n, nremaining), retiredNodes2);
                        append_assoc(retiredNodes1, retained, cons(n, append(nremaining, retiredNodes2)));
                        assert retiredNodes == append(append(retiredNodes1, retained), cons(n, append(nremaining, retiredNodes2)));
                        insert_distinct_mem(append(retiredNodes1, retained), append(nremaining, retiredNodes2), n);
                        mem_append(n, retiredNodes1, retained);
                        mem_append(n, nremaining, retiredNodes2);
                        clients_not_containsValidNode(hpLists1, n);
                        assert !containsValidNode(hpLists1, n);
                        clients_not_containsValidNode(hpLists2, n);
                        assert !containsValidNode(hpLists2, n);
                        client->retiredNodes = append(retained, nremaining);
                        close stack_client_internal(client, allClientsId, stack, _, _, _, _, _, _, _, _, _, active);
                        close clients(client, 0, allClientsId, stack, _, _, _, _, _);
                        clients_join(ch);
                        close stack_client_int(client, allClientsId, stack, 0, false, 0, append(retained, nremaining), true, nil, hpNodes, false, f);
                        assert clients(ch, 0, allClientsId, stack, allClients, allocNodes, poppedNodes, ?newRetiredNodes, ?newHpLists);
                        assert newRetiredNodes == append(retiredNodes1, append(append(retained, nremaining), retiredNodes2));
                        
                        assert hpLists == append(hpLists1, cons(hpRec(nil, append(retained, cons(n, nremaining)), hpNodes, false), hpLists2));
                        assert newHpLists == append(hpLists1, cons(hpRec(nil, append(retained, nremaining), hpNodes, false), hpLists2));
                        
                        //
                        append_assoc(retained, nremaining, retiredNodes2);
                        append_assoc(retiredNodes1, retained, append(nremaining, retiredNodes2));
                        assert newRetiredNodes == append(append(retiredNodes1, retained), append(nremaining, retiredNodes2));
                        insert_distinct_mem(append(retiredNodes1, retained), append(nremaining, retiredNodes2), n); 
                        assert !mem(n, append(retiredNodes1, retained));
                        remove_append(n, append(retiredNodes1, retained), cons(n, append(nremaining, retiredNodes2)));
                        assert newRetiredNodes == remove(n, retiredNodes); 
                        
                        list<struct node*> lhpValid = append(retained, cons(n, nremaining));
                        list<struct node*> newLhpValid = append(retained, nremaining);

                        //update foreach + prove that n is not a member of allocNodes
                        foreach_split(hpLists1, cons(hpRec(nil, lhpValid, hpNodes, false), hpLists2));
                        open foreach(cons(hpRec(nil, lhpValid, hpNodes, false), hpLists2), validLhp_helper(allClients, allocNodes, retiredNodes));
                        open validLhp_helper(allClients, allocNodes, retiredNodes)(hpRec(nil, lhpValid, hpNodes, false));
                        
                        open validLhp(allClients, allocNodes, retiredNodes, nil, lhpValid, hpNodes, false);
                        lset_union_contains(retained, cons(n, nremaining), n);
                        assert mem(n, lhpValid) == true;
                        assert take(length(allocNodes), allocNodes) == allocNodes;
                        assert lset_subset(lset_inters(allocNodes, lhpValid), lset_inters(hpNodes, lhpValid)) == true;
                        lset_subset_contains(lset_inters(allocNodes, lhpValid), lset_inters(hpNodes, lhpValid), n);
                        lset_inters_contains(hpNodes, lhpValid, n);
                        lset_inters_contains(allocNodes, lhpValid, n);
                        assert (!mem(n, allocNodes));
                        close validLhp(allClients, allocNodes, retiredNodes, nil, lhpValid, hpNodes, false);
                        
                        validLhp_remove_retired(append(retiredNodes1, retained), n, append(nremaining, retiredNodes2), retained, nremaining);
                        
                        close validLhp_helper(allClients, allocNodes, newRetiredNodes)(hpRec(nil, newLhpValid, hpNodes, false));
                        
                        foreach_validLhp_helper_remove_retired(hpLists1, allClients, allocNodes, append(retiredNodes1, retained), n, append(nremaining, retiredNodes2));
                        foreach_validLhp_helper_remove_retired(hpLists2, allClients, allocNodes, append(retiredNodes1, retained), n, append(nremaining, retiredNodes2));
                        
                        close foreach(cons(hpRec(nil, append(retained, nremaining), hpNodes, false), hpLists2), validLhp_helper(allClients, allocNodes, newRetiredNodes));
                        foreach_append(hpLists1, cons(hpRec(nil, append(retained, nremaining), hpNodes, false), hpLists2));
                        
                        //
                        lset_remove_contains(allocNodes, 0, n);
                                                
                        //remove tracker from foreach of retiredNodes
                        mem_append(n, append(retiredNodes1, retained), cons(n, append(nremaining, retiredNodes2)));
                        foreach_remove(n, retiredNodes);
                        occ_mem(allocNodes, n);
                        open node_tracker_helper(allocNodes, 0)(n);
                        open node_tracker(n, ?id, 0); 
                        destroy_cptracker(id);
                        open node_cp_helper(n, _);
                        
                        //pure 
                        remove_nomem((struct node*)0, n, retiredNodes);
                        assert !mem((struct node*)0, newRetiredNodes);
                        
                        //prove distinct(newRetiredNodes)
                        distinct_remove(n, retiredNodes);
                        assert distinct(newRetiredNodes) == true;
                        
                        //
                        switch(lset_inters(nodes, newRetiredNodes)) {
                            case cons(x, t):
                                lset_inters_contains(nodes, newRetiredNodes, x);
                                lset_union_contains(append(retiredNodes1, retained), append(nremaining, retiredNodes2), x);
                                lset_inters_contains(nodes, retiredNodes, x);
                                lset_union_contains(append(retiredNodes1, retained), cons(n, append(nremaining, retiredNodes2)), x);
                                assert false;
                            case nil:
                        } 
                        assert lset_disjoint(nodes, newRetiredNodes) == true;
                        
                        //
                        switch(lset_inters(poppedNodes, newRetiredNodes)) {
                            case cons(x, t):
                                lset_inters_contains(poppedNodes, newRetiredNodes, x);
                                lset_union_contains(append(retiredNodes1, retained), append(nremaining, retiredNodes2), x);
                                lset_inters_contains(poppedNodes, retiredNodes, x);
                                lset_union_contains(append(retiredNodes1, retained), cons(n, append(nremaining, retiredNodes2)), x);
                                assert false;
                            case nil:
                        } 
                        assert lset_disjoint(poppedNodes, newRetiredNodes) == true;
                        
                        assert !mem(n, append(retiredNodes1, retained));
                        assert !mem(n, append(nremaining, retiredNodes2));
                        lset_inters_contains(poppedNodes, retiredNodes, n);
                        assert !mem(n, poppedNodes);
                        lset_inters_contains(nodes, retiredNodes, n);
                        assert !mem(n, nodes);
                        
                        if(!lset_subset(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, newRetiredNodes)))) {
                            lset_subset_contains_conv(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, newRetiredNodes)));
                            open exwitness(?x);
                            lset_union_contains(nodes, lset_union(poppedNodes, newRetiredNodes), x);
                            lset_union_contains(poppedNodes, newRetiredNodes, x);
                            lset_union_contains(append(retiredNodes1, retained), cons(n, append(nremaining, retiredNodes2)), x);
                            lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), x);
                            lset_union_contains(nodes, lset_union(poppedNodes, retiredNodes), x);
                            lset_union_contains(poppedNodes, retiredNodes, x);                            
                            lset_union_contains(append(retiredNodes1, retained), append(nremaining, retiredNodes2), x);
                            assert false;
                        }
                        
                        close stackInternal(stack, elems, allClientsId);
                        close stack_ctor(stack, allClientsId)();
                        close atomic_noop_context_post(context)();
                    }
                @*/
                //@ close atomic_noop_context_pre(context)(stack_ctor(stack, allClientsId));
                //@ produce_lemma_function_pointer_chunk(context);
                atomic_noop();
                //@ open atomic_noop_context_post(context)();
                //@ leak is_atomic_noop_context(context);
            }
            //@ close [f]stack_helper(stack, allClientsId);
       
            release_node(stack, client, n);
        }
    }
    //@ append_nil(retained);
    //@ assert remaining == nil;
    
    linkedlist_dispose(rlist);
    
    return tmplist;
}

void deactivate_local_hazard_pointers_lemma(struct stack *stack, struct stack_client* client, struct linkedlist* hpList)
//@ requires [?f]stack_helper(stack, ?allClientsId) &*& stack_client_int(client, allClientsId, stack, 0, false, 0, ?retained, true, nil, ?hpNodes, false, f);
//@ ensures [f]stack_helper(stack, allClientsId) &*& stack_client_int(client, allClientsId, stack, 0, false, 0, retained, false, nil, nil, false, f);
{
    //@ open [f]stack_helper(stack, allClientsId);
    {
        /*@
            predicate_family_instance atomic_noop_context_pre(context)(predicate() inv) = 
                inv == stack_ctor(stack, allClientsId) &*&
                stack_client_int(client, allClientsId, stack, 0, false, 0, retained, true, nil, hpNodes, false, f);
            predicate_family_instance atomic_noop_context_post(context)() = 
                stack_client_int(client, allClientsId, stack, 0, false, 0, retained, false, nil, nil, false, f);
    
            lemma void context(): atomic_noop_context
                requires atomic_noop_context_pre(context)(?inv) &*& inv();
                ensures atomic_noop_context_post(context)() &*& inv();
            {
                open atomic_noop_context_pre(context)(inv);
                open stack_ctor(stack, allClientsId)();
                open stackInternal(stack, ?elems, allClientsId);
                assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
                open stack_client_int(client, allClientsId, stack, 0, false, 0, retained, true, nil, hpNodes, false, f);
                ghost_list_member_handle_lemma();
                clients_split(ch, client);
                open clients(client, 0, allClientsId, stack, _, _, _, _, _);
                open stack_client_internal(client, allClientsId, stack, _, ?cn, _, _, _, _, _, _, _, ?active);
                assert clients(ch, client, allClientsId, stack, ?allClients1, ?allocNodes1, ?poppedNodes1, ?retiredNodes1, ?hpLists1);
                assert clients(cn, 0, allClientsId, stack, ?allClients2, ?allocNodes2, ?poppedNodes2, ?retiredNodes2, ?hpLists2);
                client->localHpActive = false;
                client->localHpFirstCollected = false;
                client->localHpList = nil;
                close stack_client_internal(client, allClientsId, stack, _, cn, _, _, _, _, _, _, _, active);
                close clients(client, 0, allClientsId, stack, _, _, _, _, _);
                clients_join(ch);
                close stack_client_int(client, allClientsId, stack, 0, false, 0, retained, false, nil, nil, false, f);
                
                //update foreach
                foreach_split(hpLists1, cons(hpRec(nil, retained, hpNodes, false), hpLists2));
                open foreach(cons(hpRec(nil, retained, hpNodes, false), hpLists2), validLhp_helper(allClients, allocNodes, retiredNodes));
                open validLhp_helper(allClients, allocNodes, retiredNodes)(hpRec(nil, retained, hpNodes, false));
                open validLhp(allClients, allocNodes, retiredNodes, nil, retained, hpNodes, false);
                foreach_append(hpLists1, hpLists2);
                
                
                close stackInternal(stack, elems, allClientsId);
                close stack_ctor(stack, allClientsId)();
                close atomic_noop_context_post(context)();
            }
        @*/
        //@ close atomic_noop_context_pre(context)(stack_ctor(stack, allClientsId));
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_noop();
        //@ open atomic_noop_context_post(context)();
        //@ leak is_atomic_noop_context(context);
    }
    //@ close [f]stack_helper(stack, allClientsId);
}

void stack_client_reduce_fraction_lemma(struct stack *stack, struct stack_client* client)
/*@ requires [?f]stack_helper(stack, ?allClientsId) &*& exwitness<real>(?f1) &*& 0 < f1 &*& f1 < f &*&
        stack_client_int(client, allClientsId, stack, 0, false, 0, ?retired, false, nil, nil, false, f);
@*/
/*@ ensures [f1]stack_helper(stack, allClientsId) &*&
        stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1) &*& 
        [f-f1]stack_helper(stack, allClientsId) &*&
        [f-f1]stack->full_fraction_helper |-> _;
@*/
{
    //@ open [f]stack_helper(stack, allClientsId);
    //@ open exwitness<real>(f1);
    {
        /*@
        predicate_family_instance atomic_noop_context_pre(context)(predicate() inv) = 
            inv == stack_ctor(stack, allClientsId) &*&  
            0 < f1 &*& f1 < f &*&
            stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f);
        predicate_family_instance atomic_noop_context_post(context)() = 
            stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1) &*&
            [f - f1]stack->full_fraction_helper |-> _;
        lemma void context(): atomic_noop_context
            requires atomic_noop_context_pre(context)(?inv) &*& inv();
            ensures atomic_noop_context_post(context)() &*& inv();
        {
            open atomic_noop_context_pre(context)(inv);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            open stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f);
            ghost_list_member_handle_lemma();
            clients_split(ch, client);
            open clients(client, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(client, _, _, _, _, _, _, _, _, _, _, _, ?active);
            client->stack_full_fraction_helper_fraction = f1;
            close stack_client_internal(client, _, _, _, _, _, _, _, _, _, _, _, active);
            close clients(client, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
            close stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1);
               
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_noop_context_post(context)();
        }
        @*/
        //@ close atomic_noop_context_pre(context)(stack_ctor(stack, allClientsId));
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_noop();
        //@ open atomic_noop_context_post(context)();
        //@ leak is_atomic_noop_context(context);
    }
    //@ close [f1]stack_helper(stack, allClientsId);
    //@ close [f-f1]stack_helper(stack, allClientsId);
}

void stack_client_increase_fraction_lemma(struct stack *stack, struct stack_client* client)
/*@ requires [?f1]stack_helper(stack, ?allClientsId) &*&
        stack_client_int(client, allClientsId, stack, 0, false, 0, ?retired, false, nil, nil, false, f1) &*& 
        [?f2]stack_helper(stack, allClientsId) &*&
        [f2]stack->full_fraction_helper |-> _;
@*/
/*@ ensures [f1+f2]stack_helper(stack, allClientsId) &*& 
        stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1+f2);
@*/
{
    //@ open [f1]stack_helper(stack, allClientsId);
    //@ open [f2]stack_helper(stack, allClientsId);
    {
        /*@
        predicate_family_instance atomic_noop_context_pre(context)(predicate() inv) = 
            inv == stack_ctor(stack, allClientsId) &*& 
            stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1) &*&
            [f2]stack->full_fraction_helper |-> _;
        predicate_family_instance atomic_noop_context_post(context)() = 
            stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1+f2);
        lemma void context(): atomic_noop_context
            requires atomic_noop_context_pre(context)(?inv) &*& inv();
            ensures atomic_noop_context_post(context)() &*& inv();
        {
            open atomic_noop_context_pre(context)(inv);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            open stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1);
            ghost_list_member_handle_lemma();
            clients_split(ch, client);
            open clients(client, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(client, _, _, _, _, _, _, _, _, _, _, _, ?active);
            client->stack_full_fraction_helper_fraction = f1+f2;            
            close stack_client_internal(client, _, _, _, _, _, _, _, _, _, _, _, active);
            close clients(client, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
            close stack_client_int(client, allClientsId, stack, 0, false, 0, retired, false, nil, nil, false, f1+f2);
               
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_noop_context_post(context)();
        }
        @*/
        //@ close atomic_noop_context_pre(context)(stack_ctor(stack, allClientsId));
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_noop();
        //@ open atomic_noop_context_post(context)();
        //@ leak is_atomic_noop_context(context);
    }
    //@ close [f1 + f2]stack_helper(stack, allClientsId);
}


struct stack_client* get_first_stack_client_non_null(struct stack *stack, struct stack_client* client)
/*@ requires [?f]stack_helper(stack, ?allClientsId) &*& 
        stack_client_int(client, allClientsId, stack, ?hp, ?hpAlloc, ?popped, ?retired, ?lhpA, ?lhpR, ?lhps, ?lhpFcc, f);
@*/
/*@ ensures [f]stack_helper(stack, allClientsId) &*& 
        stack_client_int(client, allClientsId, stack, hp, hpAlloc, popped, retired, lhpA, lhpR, lhps, lhpFcc, f) &*&
        [_]ghost_list_member_handle(allClientsId, result) &*& result != 0;
@*/
{
    //@ open [f] stack_helper(stack, allClientsId);
    struct stack_client *sc = 0;
    //@ struct stack_client *schProphecy = create_prophecy_pointer();
    {
        /*@
        predicate_family_instance atomic_load_pointer_context_pre(context)(predicate() inv, void **pp, void *prophecy) =
            inv == stack_ctor(stack, allClientsId) &*&
            pp == &stack->clients &*& 
            prophecy == schProphecy &*&
            stack_client_int(client, allClientsId, stack, hp, hpAlloc, popped, retired, lhpA, lhpR, lhps, lhpFcc, f);
        predicate_family_instance atomic_load_pointer_context_post(context)() = 
            stack_client_int(client, allClientsId, stack, hp, hpAlloc, popped, retired, lhpA, lhpR, lhps, lhpFcc, f) &*&
            schProphecy != 0 &*&
            [_]ghost_list_member_handle(allClientsId, schProphecy);
        lemma void context(atomic_load_pointer_operation *op) : atomic_load_pointer_context
            requires
                atomic_load_pointer_context_pre(context)(?inv, ?pp, ?prophecy) &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_pre(op)(pp, prophecy);
            ensures
                atomic_load_pointer_context_post(context)() &*& inv() &*&
                is_atomic_load_pointer_operation(op) &*& atomic_load_pointer_operation_post(op)();
        {
            open atomic_load_pointer_context_pre(context)(inv, pp, prophecy);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            open stack_client_int(client, allClientsId, stack, hp, hpAlloc, popped, retired, lhpA, lhpR, lhps, lhpFcc, f);
            ghost_list_member_handle_lemma();
            close stack_client_int(client, allClientsId, stack, hp, hpAlloc, popped, retired, lhpA, lhpR, lhps, lhpFcc, f);
            op();
            open clients(ch, 0, allClientsId, stack, _, _, _, _, _);
            open stack_client_internal(ch, _, _, _, _, _, _, _, _, _, _, _, ?active);
            close stack_client_internal(ch, _, _, _, _, _, _, _, _, _, _, _, active);
            close clients(ch, 0, allClientsId, stack, _, _, _, _, _);
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_load_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_load_pointer_context_pre(context)(stack_ctor(stack, allClientsId), &stack->clients, schProphecy);
        //@ produce_lemma_function_pointer_chunk(context);
        sc = atomic_load_pointer(&stack->clients);
        //@ open atomic_load_pointer_context_post(context)();
        //@ leak is_atomic_load_pointer_context(context);
    }
    //@ close [f] stack_helper(stack, allClientsId);
    return sc;
}

void move_retired_lemma(struct stack *stack, struct stack_client* client1, struct stack_client* client2)
/*@ requires [?f]stack_helper(stack, ?allClientsId) &*&
        stack_client_int(client1, allClientsId, stack, 0, false, 0, ?retired1, false, nil, nil, false, ?f1) &*& 
        stack_client_int(client2, allClientsId, stack, 0, false, 0, ?retired2, false, nil, nil, false, ?f2);
@*/
/*@ ensures [f]stack_helper(stack, allClientsId)  &*&
        stack_client_int(client1, allClientsId, stack, 0, false, 0, append(retired1, retired2), false, nil, nil, false, f1) &*& 
        stack_client_int(client2, allClientsId, stack, 0, false, 0, nil, false, nil, nil, false, f2);
@*/
{
    //@ open [f]stack_helper(stack, allClientsId);
    {
        /*@
        predicate_family_instance atomic_noop_context_pre(context)(predicate() inv) = 
            inv == stack_ctor(stack, allClientsId) &*& 
            stack_client_int(client1, allClientsId, stack, 0, false, 0, retired1, false, nil, nil, false, f1) &*&
            stack_client_int(client2, allClientsId, stack, 0, false, 0, retired2, false, nil, nil, false, f2);
        predicate_family_instance atomic_noop_context_post(context)() = 
            stack_client_int(client1, allClientsId, stack, 0, false, 0, append(retired1, retired2), false, nil, nil, false, f1) &*&
            stack_client_int(client2, allClientsId, stack, 0, false, 0, nil, false, nil, nil, false, f2);
        lemma void context(): atomic_noop_context
            requires atomic_noop_context_pre(context)(?inv) &*& inv();
            ensures atomic_noop_context_post(context)() &*& inv();
        {
            open atomic_noop_context_pre(context)(inv);
            open stack_ctor(stack, allClientsId)();
            open stackInternal(stack, ?elems, allClientsId);
            assert stack->head |-> ?head &*& lseg(head, 0, ?nodes, elems);
            assert stack->clients |-> ?ch &*& clients(ch, 0, allClientsId, stack, ?allClients, ?allocNodes, ?poppedNodes, ?retiredNodes, ?hpLists);
            clients_distinct(ch);
            
            open stack_client_int(client1, allClientsId, stack, 0, false, 0, retired1, false, nil, nil, false, f1);
            ghost_list_member_handle_lemma_helper(allClientsId, client1);
            close stack_client_int(client1, allClientsId, stack, 0, false, 0, retired1, false, nil, nil, false, f1);
            open stack_client_int(client2, allClientsId, stack, 0, false, 0, retired2, false, nil, nil, false, f2);
            ghost_list_member_handle_lemma_helper(allClientsId, client2);
            close stack_client_int(client2, allClientsId, stack, 0, false, 0, retired2, false, nil, nil, false, f2);
            
            clients_split(ch, client1);
            
            open clients(client1, 0, allClientsId, stack, _, _, _, _, _);
            
            if(client1 == client2) {
                stack_client_match2(client1);
                open stack_client_int(client1, allClientsId, stack, 0, false, 0, retired1, false, nil, nil, false, f1);
                open stack_client_int(client2, allClientsId, stack, 0, false, 0, retired2, false, nil, nil, false, f2);
                open stack_client_internal(client1, _, _, _, ?c1Next, _, _, _, _, _, _, _, ?active);
                assert false;
            } 
            
            open stack_client_internal(client1, _, _, _, ?c1Next, _, _, _, _, _, _, _, ?active);
            open stack_client_int(client1, allClientsId, stack, 0, false, 0, retired1, false, nil, nil, false, f1);
            client1->retiredNodes = append(retired1, retired2);
            close stack_client_internal(client1, _, _, _, _, _, _, _, _, _, _, _, active);
            close stack_client_int(client1, allClientsId, stack, 0, false, 0, append(retired1, retired2), false, nil, nil, false, f1);
            
            assert clients(ch, client1, allClientsId, stack, ?allClients1, ?allocNodes1, ?poppedNodes1, ?retiredNodes1, ?hpLists1);
            assert clients(c1Next, 0, allClientsId, stack, ?allClients2, ?allocNodes2, ?poppedNodes2, ?retiredNodes2, ?hpLists2);
            
            mem_append(client2, allClients1, cons(client1, allClients2));
            if(mem(client2, allClients2)) {
                clients_split(c1Next, client2);
                open clients(client2, 0, allClientsId, stack, _, _, _, _, _);
                open stack_client_internal(client2, _, _, _, ?c2Next, _, _, _, _, _, _, _, ?active2);
                open stack_client_int(client2, allClientsId, stack, 0, false, 0, retired2, false, nil, nil, false, f2);
                client2->retiredNodes = nil;
                close stack_client_int(client2, allClientsId, stack, 0, false, 0, nil, false, nil, nil, false, f2);
                close stack_client_internal(client2, _, _, _, c2Next, _, _, _, _, _, _, _, active2);
                assert clients(c1Next, client2, allClientsId, stack, ?allClients3, ?allocNodes3, ?poppedNodes3, ?retiredNodes3, ?hpLists3);
                assert clients(c2Next, 0, allClientsId, stack, ?allClients4, ?allocNodes4, ?poppedNodes4, ?retiredNodes4, ?hpLists4);
                close clients(client2, 0, allClientsId, stack, _, _, _, _, _);                
                clients_join(c1Next);

                if(!lmultiset_equals(retiredNodes, append(retiredNodes1, append(append(retired1,retired2), append(retiredNodes3, retiredNodes4))))) {
                    lmultiset_equals_occ_conv(retiredNodes, append(retiredNodes1, append(append(retired1,retired2), append(retiredNodes3, retiredNodes4)))); 
                    open exwitness(?x);
                    lmultiset_union_occ(retiredNodes1, append(append(retired1,retired2), append(retiredNodes3, retiredNodes4)), x);
                    lmultiset_union_occ(append(retired1,retired2), append(retiredNodes3, retiredNodes4), x);
                    lmultiset_union_occ(retired1,retired2, x);
                    lmultiset_union_occ(retiredNodes3, retiredNodes4, x);
                    lmultiset_union_occ(retiredNodes1, append(retired1, append(retiredNodes3, append(retired2, retiredNodes4))), x);
                    lmultiset_union_occ(retired1, append(retiredNodes3, append(retired2, retiredNodes4)), x);
                    lmultiset_union_occ(retiredNodes3, append(retired2, retiredNodes4), x);
                    lmultiset_union_occ(retired2, retiredNodes4, x);
                    assert false;
                }
            } else {
                clients_last_nomem(ch, client1);
                assert mem(client2, allClients1) == true;
                clients_split2(ch, client2, client1);
                open clients(client2, client1, allClientsId, stack, _, _, _, _, _);
                open stack_client_int(client2, allClientsId, stack, 0, false, 0, retired2, false, nil, nil, false, f2);
                open stack_client_internal(client2, _, _, _, ?c2Next, _, _, _, _, _, _, _, ?active2);
                client2->retiredNodes = nil;
                assert clients(ch, client2, allClientsId, stack, ?allClients3, ?allocNodes3, ?poppedNodes3, ?retiredNodes3, ?hpLists3);
                assert clients(c2Next, client1, allClientsId, stack, ?allClients4, ?allocNodes4, ?poppedNodes4, ?retiredNodes4, ?hpLists4);
                close stack_client_internal(client2, _, _, _, c2Next, _, _, _, _, _, _, _, active2);
                close stack_client_int(client2, allClientsId, stack, 0, false, 0, nil, false, nil, nil, false, f2);
                close clients(client2, client1, allClientsId, stack, _, _, _, _, _);
                mem_append(client1, allClients3, cons(client2, allClients4));
                clients_join2(ch, client1);
                
                assert retiredNodes1 == append(retiredNodes3, append(retired2, retiredNodes4));
                assert retiredNodes == append(retiredNodes1, append(retired1, retiredNodes2));
                
                list<struct node*> newRetiredNodes1 = append(retiredNodes3, retiredNodes4);
                list<struct node*> nRetiredNodes = append(newRetiredNodes1, append(append(retired1, retired2), retiredNodes2));
                
                if(!lmultiset_equals(retiredNodes, nRetiredNodes)) {
                    lmultiset_equals_occ_conv(retiredNodes, nRetiredNodes); 
                    open exwitness(?x);
                    lmultiset_union_occ(newRetiredNodes1, append(append(retired1, retired2), retiredNodes2), x);
                    lmultiset_union_occ(retiredNodes3, retiredNodes4, x);
                    lmultiset_union_occ(append(retired1, retired2), retiredNodes2, x);
                    lmultiset_union_occ(retired1, retired2, x);
                    
                    lmultiset_union_occ(retiredNodes1, append(retired1, retiredNodes2), x);
                    lmultiset_union_occ(retiredNodes3, append(retired2, retiredNodes4), x);
                    lmultiset_union_occ(retired2, retiredNodes4, x);
                    lmultiset_union_occ(retired1, retiredNodes2, x);
                    assert false;
                }
            }
            
            close clients(client1, 0, allClientsId, stack, _, _, _, _, _);
            clients_join(ch);
            
            assert clients(ch, 0, allClientsId, stack, allClients, allocNodes, poppedNodes, ?newRetiredNodes, hpLists);
            assert lmultiset_equals(retiredNodes, newRetiredNodes)==true;
            lmultiset_equals_lset_equals(retiredNodes, newRetiredNodes);
            
            foreach_validLhp_helper_rearrange_retired(hpLists, allClients, allocNodes, retiredNodes, newRetiredNodes);
            
            foreach_lmultiset_equals(retiredNodes, newRetiredNodes);
            
            lset_equals_contains(retiredNodes, newRetiredNodes, 0);
            
            if(!distinct(newRetiredNodes)) {
                lmultiset_occ_distinct_conv(newRetiredNodes);
                open exwitness(?x);
                lmultiset_occ_distinct(retiredNodes, x);
                lmultiset_equals_occ(retiredNodes, newRetiredNodes, x);
                assert false;
            }
            
            switch(lset_inters(nodes, newRetiredNodes)) {
                case cons(x, t):
                    lset_inters_contains(nodes, newRetiredNodes, x);
                    lset_inters_contains(nodes, retiredNodes, x);
                    lset_equals_contains(retiredNodes, newRetiredNodes, x);
                    assert false;
                case nil:
            }
            
            switch(lset_inters(poppedNodes, newRetiredNodes)) {
                case cons(x, t): 
                    lset_inters_contains(poppedNodes, newRetiredNodes, x);
                    lset_inters_contains(poppedNodes, retiredNodes, x);
                    lset_equals_contains(retiredNodes, newRetiredNodes, x);
                    assert false;
                case nil:
            }
            
            if(!lset_subset(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, newRetiredNodes)))) {
                lset_subset_contains_conv(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, newRetiredNodes)));
                open exwitness(?x);
                lset_subset_contains(lset_remove(allocNodes, 0), lset_union(nodes, lset_union(poppedNodes, retiredNodes)), x);
                lset_union_contains(nodes, lset_union(poppedNodes, retiredNodes), x);
                lset_union_contains(poppedNodes, retiredNodes, x);
                lset_union_contains(nodes, lset_union(poppedNodes, newRetiredNodes), x);
                lset_union_contains(poppedNodes, newRetiredNodes, x);
                lset_equals_contains(retiredNodes, newRetiredNodes, x);
                assert false;
            }
            
            close stackInternal(stack, elems, allClientsId);
            close stack_ctor(stack, allClientsId)();
            close atomic_noop_context_post(context)();
        }
        @*/
        //@ close atomic_noop_context_pre(context)(stack_ctor(stack, allClientsId));
        //@ produce_lemma_function_pointer_chunk(context);
        atomic_noop();
        //@ open atomic_noop_context_post(context)();
        //@ leak is_atomic_noop_context(context);
    }
    //@ close [f]stack_helper(stack, allClientsId);
}

void collect_retired_nodes(struct stack *stack, struct stack_client* client)
/*@ requires [?f]stack_helper(stack, ?allClientsId) &*& 
        stack_client_int(client, allClientsId, stack, 0, false, 0, ?retired, false, nil, nil, false, f) &*&
        client->rlist |-> ?rList &*& linkedlist(rList, retired);
@*/
/*@ ensures [f]stack_helper(stack, allClientsId) &*& exwitness(?newRetired) &*&
        stack_client_int(client, allClientsId, stack, 0, false, 0, append(retired, newRetired), false, nil, nil, false, f) &*&
        client->rlist |-> rList &*& linkedlist(rList, append(retired, newRetired));
@*/
{
    struct linkedlist* rlist = client->rlist;
    
    struct stack_client *sc = get_first_stack_client_non_null(stack, client);
    //@ list<struct node*> added = nil;
    //@ append_nil(retired);
    while(sc!=0)
    /*@ invariant [f]stack_helper(stack, allClientsId) &*& 
            stack_client_int(client, allClientsId, stack, 0, false, 0, ?newRetired, false, nil, nil, false, f) &*& 
            linkedlist(rlist, newRetired) &*&
            newRetired == append(retired, added) &*&
            (sc == 0 ? true : [_]ghost_list_member_handle(allClientsId, sc));
    @*/
    {
        //@ close exwitness(f/2);
        //@ open [f]stack_helper(stack, allClientsId); //expose 0 < f
        //@ close [f]stack_helper(stack, allClientsId);
        stack_client_reduce_fraction_lemma(stack, client);
        bool acquired = try_acquire_stack_client(stack, sc);
        if(acquired) {
            //@ open stack_client(sc, allClientsId, stack, 0, false, 0, f/2);
            
            move_retired_lemma(stack, client, sc);
            
            struct linkedlist* otherRList = sc->rlist;
            //@ assert linkedlist(otherRList, ?retired2);
            //@ list<struct node*> added2 = nil;
            //@ append_nil(newRetired);
            while(!linkedlist_is_empty(otherRList)) 
            /*@ invariant linkedlist(otherRList, ?remaining) &*& retired2 == append(added2, remaining) &*&
                    linkedlist(rlist, append(newRetired, added2));
            @*/
            {
                //@ switch(remaining) { case nil: case cons(h,t): }
                struct node* node = linkedlist_pop(otherRList);
                //@ assert linkedlist(otherRList, ?newRemaining); 
                linkedlist_add_end(rlist, node);
                //@ append_cons_r_snoc_l(added2, node, newRemaining);
                //@ append_assoc(newRetired, added2, cons(node, nil));
                //@ added2 = snoc(added2, node);
            }
            //@ close stack_client(sc, allClientsId, stack, 0, false, 0, f/2);
            
            //@ append_assoc(retired, added, retired2);
            //@ added = append(added, retired2);
            
            //@ close stack_with_client(stack, sc, f/2);
            stack_dispose_client(stack, sc);
            //@ open [f/2]stack_free(stack);
            //@ open [f/2]stack_helper(stack, allClientsId);
            //@ open [f/2]stack_helper(stack, _);
            //@ close [f/2]stack_helper(stack, allClientsId);
            //@ close [f/2]stack_helper(stack, allClientsId);
        }
        stack_client_increase_fraction_lemma(stack, client);
        
        sc = get_next_stack_client(stack, sc);
    }
    //@ close exwitness(added);
}

void scan(struct stack *stack, struct stack_client* client)
//@ requires [?f]stack_helper(stack, ?allClientsId) &*& stack_client(client, allClientsId, stack, 0, false, 0, f);
//@ ensures [f]stack_helper(stack, allClientsId) &*& stack_client(client, allClientsId, stack, 0, false, 0, f);
{
    //@ open stack_client(client, allClientsId, stack, 0, false, 0, f);
    
    //0. collect retired nodes of deactivated stack clients
    collect_retired_nodes(stack, client);
    //@ open exwitness(_);
    
    //1. collect hazard nodes in thread-local data structure

    struct linkedlist* hpList = collect_hazard_pointers(stack, client);

    //2. free all deleted nodes that are not hazard nodes according to thread-local data structure
    
    struct linkedlist* rlist = client->rlist;
    struct linkedlist* tmplist = free_retired_nodes(stack, client, hpList, rlist); 
    client->rlist = tmplist;

    //3. dispose local hazard pointers
    
    deactivate_local_hazard_pointers_lemma(stack, client, hpList);
    linkedlist_dispose(hpList);

    //@ close stack_client(client, allClientsId, stack, 0, false, 0, f);
}

void release_node(struct stack *stack, struct stack_client *client, struct node* node)
    //@ requires [?f]stack_helper(stack, ?allClientsId) &*& stack_client_int(client, allClientsId, stack, 0, false, 0, ?retired, ?hpActive, ?hpRem, ?hpList, ?fcc, f) &*& node(node, _, _, _);
    //@ ensures [f]stack_helper(stack, allClientsId) &*& stack_client_int(client, allClientsId, stack, 0, false, 0, retired, hpActive, hpRem, hpList, fcc, f);
{
    free(node);
}

