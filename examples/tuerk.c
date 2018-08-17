// Illustrates VeriFast's implementation of the alternative loop proof rule proposed by [1].
// [1] Thomas Tuerk. Local Reasoning about While-Loops. VS-Theory workshop at VSTTE 2010.

struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *node; list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, ?values0) &*& values == cons(value, values0);

lemma_auto void nodes_inv()
    requires nodes(?node, ?values);
    ensures nodes(node, values) &*& (values == nil) == (node == 0);
{
    open nodes(node, values);
}

@*/

int list_length_rec(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    //@ open nodes(node, values);
    if (node == 0)
        return 0;
    else {
        int length0 = list_length_rec(node->next);
        return 1 + length0;
    }
}

int list_length_iter(struct node *node, int *foo)
    //@ requires nodes(node, ?values) &*& integer(foo, ?x);
    //@ ensures nodes(node, values) &*& integer(foo, x) &*& result == length(values);
{
    int i = 0;
    while (node != 0)
        //@ requires nodes(node, ?values1);
        //@ ensures nodes(old_node, values1) &*& i == old_i + length(values1);
        //@ decreases length(values1);
    {
        node = node->next;
        i++;
    }
    return i;
}

/* TODO:

int list_length_iter_return(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    for (;;)
        //@ requires nodes(node, ?values);
        //@ ensures nodes(old_node, values) &*& i == old_i + length(values);
        //@ decreases length(values) - i;
    {
        if (node == 0)
            return i;
        node = node->next;
        i++;
    }
}

*/
