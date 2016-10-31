#include "stdlib.h"
#include "malloc.h"
#include "threading.h"
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
        t->left |-> ?left &*& t->right |-> ?right &*& t->value |-> _ &*& malloc_block_tree(t) &*&
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

typedef int fold_function(int acc, int x);
    //@ requires true;
    //@ ensures true;

int tree_fold(struct tree *tree, fold_function *f, int acc)
    //@ requires tree(tree, ?depth) &*& is_fold_function(f) == true;
    //@ ensures tree(tree, depth);
{
    if (tree == 0) {
        return acc;
    } else {
        //@ open tree(tree, depth);
        acc = tree_fold(tree->left, f, acc);
        acc = tree_fold(tree->right, f, acc);
        acc = f(acc, tree->value);
        return acc;
        //@ close tree(tree, depth);
    }
}

struct fold_data {
    struct thread *thread;
    struct tree *tree;
    fold_function *f;
    int acc;
};

/*@

predicate_family_instance thread_run_pre(folder)(struct fold_data *data, any info) =
    data->tree |-> ?tree &*& tree(tree, _) &*& data->f |-> ?f &*& is_fold_function(f) == true &*& data->acc |-> _;
predicate_family_instance thread_run_post(folder)(struct fold_data *data, any info) =
    data->tree |-> ?tree &*& tree(tree, _) &*& data->f |-> ?f &*& is_fold_function(f) == true &*& data->acc |-> _;

@*/

void folder(struct fold_data *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(folder)(data, ?info);
    //@ ensures thread_run_post(folder)(data, info);
{
    //@ open thread_run_pre(folder)(data, info);
    int acc = tree_fold(data->tree, data->f, data->acc);
    data->acc = acc;
    //@ close thread_run_post(folder)(data, info);
}

struct fold_data *start_fold_thread(struct tree *tree, fold_function *f, int acc)
    //@ requires tree(tree, _) &*& is_fold_function(f) == true;
    //@ ensures result->thread |-> ?t &*& thread(t, folder, result, _);
{
    struct fold_data *data = malloc(sizeof(struct fold_data));
    struct thread *t = 0;
    if (data == 0) abort();
    //@ leak malloc_block_fold_data(data);
    data->tree = tree;
    data->f = f;
    data->acc = acc;
    //@ close thread_run_pre(folder)(data, unit);
    t = thread_start_joinable(folder, data);
    data->thread = t;
    return data;
}

int join_fold_thread(struct fold_data *data)
    //@ requires data->thread |-> ?t &*& thread(t, folder, data, _);
    //@ ensures true;
{
    thread_join(data->thread);
    //@ open thread_run_post(folder)(data, _);
    return data->acc;
    //@ leak data->tree |-> ?tree &*& [_]tree(tree, _) &*& data->f |-> _ &*& data->acc |-> _ &*& data->thread |-> _;
}

int sum_function(int acc, int x) //@ : fold_function
    //@ requires true;
    //@ ensures true;
{
    int f = fac(x);
    return acc + f;
}

int product_function(int acc, int x) //@ : fold_function
    //@ requires true;
    //@ ensures true;
{
    int f = fac(x);
    return acc * f;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct tree *tree = make_tree(22);
    //@ open tree(tree, _);
    struct fold_data *leftData = start_fold_thread(tree->left, sum_function, 0);
    struct fold_data *rightData = start_fold_thread(tree->right, sum_function, 0);
    int sumLeft = join_fold_thread(leftData);
    int sumRight = join_fold_thread(rightData);
    int f = fac(tree->value);
    //@ leak tree->left |-> _ &*& tree->right |-> _ &*& tree->value |-> _ &*& malloc_block_tree(tree);
    printf("%i", sumLeft + sumRight + f);
    return 0;
}