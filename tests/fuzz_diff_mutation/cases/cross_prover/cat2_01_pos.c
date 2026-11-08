/*@
inductive tree = leaf | node(int, tree, tree);
fixpoint int tree_size(tree t) {
    switch (t) {
        case leaf: return 0;
        case node(v, left, right): return 1 + tree_size(left) + tree_size(right);
    }
}

inductive my_nat = zero | succ(my_nat);
fixpoint my_nat add_nat(my_nat a, my_nat b) {
    switch (a) {
        case zero: return b;
        case succ(prev): return succ(add_nat(prev, b));
    }
}

inductive my_list = my_nil | my_cons(int, my_list);
fixpoint int my_len(my_list l) {
    switch (l) {
        case my_nil: return 0;
        case my_cons(h, t): return 1 + my_len(t);
    }
}

inductive my_pair = my_pair(int, int);
@*/
void f()
//@ requires true;
//@ ensures tree_size(node(5, leaf, leaf)) == 1;
{}
