#include "stdlib.h"
#include "malloc.h"
#include "stdio.h"

int rand();
    //@ requires true;
    //@ ensures true;

int fac(int x)
    //@ requires true;
    //@ ensures true;
{
    int result = 1;
    while (x > 1)
        //@ invariant true;
    {
        result = result * x;
        x = x - 1;
    }
    return result;
}

struct tree {
    struct tree *left;
    struct tree *right;
    int value;
};

/*@
predicate tree(struct tree *t, int depth) =
    t == 0 ?
        depth == 0
    :
        t->left |-> ?left &*& t->right |-> ?right &*& t->value |-> ?value &*& malloc_block_tree(t) &*&
        tree(left, depth - 1) &*& tree(right, depth - 1);
@*/

struct tree *make_tree(int depth)
    //@ requires true;
    //@ ensures tree(result, depth);
{
    if (depth == 0) {
        //@ close tree(0, 0);
        return 0;
    } else {
        struct tree *left = make_tree(depth - 1);
        struct tree *right = make_tree(depth - 1);
        int value = rand();
        struct tree *t = malloc(sizeof(struct tree));
        if (t == 0) abort();
        t->left = left;
        t->right = right;
        t->value = value % 2000;
        //@ close tree(t, depth);
        return t;
    }
}

int tree_compute_sum_facs(struct tree *tree)
    //@ requires tree(tree, ?depth);
    //@ ensures tree(tree, depth);
{
    if (tree == 0) {
        return 1;
    } else {
        //@ open tree(tree, depth);
        int leftSum = tree_compute_sum_facs(tree->left);
        int rightSum = tree_compute_sum_facs(tree->right);
        int f = fac(tree->value);
        return leftSum + rightSum + f;
        //@ close tree(tree, depth);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct tree *tree = make_tree(22);
    int sum = tree_compute_sum_facs(tree);
    //@ leak tree(tree, _);
    printf("%i", sum);
    return 0;
}