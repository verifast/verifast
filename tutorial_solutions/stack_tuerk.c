struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        0 < count &*&
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*&
        nodes(next, count - 1);

@*/

struct stack {
    struct node *head;
};

/*@

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

@*/

int stack_get_count(struct stack *stack)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count) &*& result == count;
{
    //@ open stack(stack, count);
    struct node *n = stack->head;
    int i = 0;
    for (;;)
        //@ requires nodes(n, ?count1);
        //@ ensures nodes(old_n, count1) &*& i == old_i + count1;
    {
        //@ open nodes(n, count1);
        if (n == 0) {
            //@ close nodes(n, count1);
            break;
        }
        n = n->next;
        i++;
        //@ recursive_call();
        //@ close nodes(old_n, count1);
    }
    //@ close stack(stack, count);
    return i;
}
