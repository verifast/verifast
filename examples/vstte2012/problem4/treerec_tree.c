#include "stdlib.h"
#include "treerec_tree.h"

struct tree {
    struct tree *left;
    struct tree *right;
};

/*@

predicate tree(struct tree *t; tree value) =
    t == 0 ?
        value == leaf
    :
        t->left |-> ?left &*& t->right |-> ?right &*& malloc_block_tree(t) &*&
        tree(left, ?vl) &*& tree(right, ?vr) &*&
        value == node(vl, vr);

@*/

struct tree *create_leaf()
    //@ requires true;
    //@ ensures tree(result, leaf);
{
    return 0;
}

struct tree *create_node(struct tree *left, struct tree *right)
    //@ requires tree(left, ?valueLeft) &*& tree(right, ?valueRight);
    //@ ensures tree(result, node(valueLeft, valueRight));
{
    struct tree *result = malloc(sizeof(struct tree));
    if (result == 0) abort();
    result->left = left;
    result->right = right;
    return result;
}

bool tree_is_leaf(struct tree *t)
    //@ requires tree(t, ?value);
    //@ ensures tree(t, value) &*& result == (value == leaf);
{
    //@ open tree(t, _);
    return t == 0;
}

void tree_destruct_node(struct tree *t, struct tree **left, struct tree **right)
    //@ requires tree(t, ?value) &*& value != leaf &*& *left |-> _ &*& *right |-> _;
    /*@
    ensures
        switch (value) {
            case leaf: return false;
            case node(vl, vr): return
                *left |-> ?l &*& tree(l, vl) &*&
                *right |-> ?r &*& tree(r, vr);
        };
    @*/
{
    //@ open tree(t, _);
    *left = t->left;
    *right = t->right;
    free(t);
}

void tree_dispose(struct tree *t)
    //@ requires tree(t, ?value);
    //@ ensures true;
{
    if (t != 0) {
        tree_dispose(t->left);
        tree_dispose(t->right);
        free(t);
    }
}