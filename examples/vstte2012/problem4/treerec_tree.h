#ifndef TREEREC_TREE_H
#define TREEREC_TREE_H

/*@

inductive tree = leaf | node(tree, tree);

@*/

struct tree;

//@ predicate tree(struct tree *t; tree value);

struct tree *create_leaf();
    //@ requires true;
    //@ ensures tree(result, leaf);

struct tree *create_node(struct tree *left, struct tree *right);
    //@ requires tree(left, ?valueLeft) &*& tree(right, ?valueRight);
    //@ ensures tree(result, node(valueLeft, valueRight));

bool tree_is_leaf(struct tree *t);
    //@ requires tree(t, ?value);
    //@ ensures tree(t, value) &*& switch (value) { case leaf: return result == true; case node(l, r): return result == false; };

void tree_destruct_node(struct tree *t, struct tree **left, struct tree **right);
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

void tree_dispose(struct tree *t);
    //@ requires tree(t, ?value);
    //@ ensures true;

#endif