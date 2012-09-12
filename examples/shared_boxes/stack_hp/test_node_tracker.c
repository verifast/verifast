//@ #include "cperm_ex.gh"


struct node {
    void *data;
    struct node *next;
    //@ int trackerId; 
};


/*@
predicate node(struct node *node; struct node *next, void *data, int trackerId) = 
    malloc_block_node(node) &*&
    node != 0 &*&
    node->next |-> next &*&
    node->data |-> data &*&
    node->trackerId |-> trackerId;
    
predicate node_helper(struct node *node; pair<pair<struct node *, void*> , int> out) =
    node(node, ?next, ?data, ?trackerId) &*&
    out == pair(pair(next, data), trackerId);

lemma void node_helper_store_trackerId(struct node *node, int trackerId)
    requires node_helper(node, ?p);
    ensures node_helper(node, pair(fst(p), trackerId));
{
    open node_helper(node, p);
    open node(node, _, _, _);
    node->trackerId = trackerId;
    close node(node, _, _, _);
    close node_helper(node, _);
}

lemma void create_node_helper_tracker(struct node* node)
    requires node(node, ?next, ?data, _);
    ensures object_tracker(node_helper, node, 0, pair(next, data));
{
    close node_helper(node, _);
    produce_lemma_function_pointer_chunk(node_helper_store_trackerId) 
        : object_set_trackerId<struct node*, pair<struct node*, void*> >(node_helper)(arg1, arg2) { call(); } 
    {
        create_object_tracker(node_helper, node);
    }
}

lemma void test(struct node* node) 
    requires node(node, _, _, _);
    ensures node(node, _, _, _);
{
    create_node_helper_tracker(node);
    
    destroy_object_tracker(node_helper, node);

    open node_helper(node, _);
}
@*/
