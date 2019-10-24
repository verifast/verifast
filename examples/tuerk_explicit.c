// Illustrates VeriFast's implementation of the alternative loop proof rule proposed by [1].
// [1] Thomas Tuerk. Local Reasoning about While-Loops. VS-Theory workshop at VSTTE 2010.

struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, ?values0) &*& values == cons(value, values0);

lemma_auto void nodes_inv()
    requires nodes(?node, ?values);
    ensures nodes(node, values) &*& (values == nil) == (node == 0);
{
    open nodes(node, values);
    close nodes(node, values);
}

@*/

int list_length(struct node *node, int *foo)
    //@ requires nodes(node, ?values) &*& integer(foo, ?x);
    //@ ensures nodes(node, values) &*& integer(foo, x) &*& result == length(values);
{
    int i = 0;
    while (node != 0)
        //@ requires nodes(node, ?values1);
        //@ ensures nodes(old_node, values1) &*& i == old_i + length(values1);
        //@ decreases length(values1);
    {
        //@ open nodes(node, values1);
        node = node->next;
        i++;
        //@ recursive_call();
        //@ close nodes(old_node, values1);
    }
    return i;
}

int list_length_alt(struct node *node, int *foo)
    //@ requires nodes(node, ?values) &*& integer(foo, ?x);
    //@ ensures nodes(node, values) &*& integer(foo, x) &*& result == length(values);
{
    int i;
    for (i = 0; node != 0; node = node->next, i++)
        //@ requires nodes(node, ?values1);
        //@ ensures nodes(old_node, values1) &*& i == old_i + length(values1);
        //@ decreases length(values1);
    {
        //@ open nodes(node, values1);
        //@ recursive_call();
        //@ close nodes(old_node, values1);
    }
    return i;
}
