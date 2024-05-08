#include "stdlib.h"
#include "malloc.h"
#include "stdio.h"
#include "threading.h"

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

struct sum_data {
    struct thread *thread;
    struct tree *tree;
    int sum;
};

/*@

predicate_family_instance thread_run_pre(summator)(struct sum_data *data, any info) =
    data->tree |-> ?tree &*& tree(tree, _) &*& data->sum |-> _;
predicate_family_instance thread_run_post(summator)(struct sum_data *data, any info) =
    data->tree |-> ?tree &*& tree(tree, _) &*& data->sum |-> ?sum;

@*/

void summator(struct sum_data *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(summator)(data, ?info);
    //@ ensures thread_run_post(summator)(data, info);
{
    //@ open thread_run_pre(summator)(data, info);
    int sum = tree_compute_sum_facs(data->tree);
    data->sum = sum;
    //@ close thread_run_post(summator)(data, info);
}

struct sum_data *start_sum_thread(struct tree *tree)
    //@ requires tree(tree, _);
    //@ ensures result->thread |-> ?t &*& thread(t, summator, result, _);
{
    struct sum_data *data = malloc(sizeof(struct sum_data));
    struct thread *t = 0;
    if (data == 0) abort();
    //@ leak malloc_block_sum_data(data);
    data->tree = tree;
    //@ close thread_run_pre(summator)(data, unit);
    t = thread_start_joinable(summator, data);
    data->thread = t;
    return data;
}

int join_sum_thread(struct sum_data *data)
    //@ requires data->thread |-> ?t &*& thread(t, summator, data, _);
    //@ ensures true;
{
    thread_join(data->thread);
    //@ open thread_run_post(summator)(data, _);
    return data->sum;
    //@ leak data->tree |-> ?tree &*& tree(tree, _) &*& data->sum |-> _ &*& data->thread |-> _;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct tree *tree = make_tree(22);
    //@ open tree(tree, _);
    struct sum_data *leftData = start_sum_thread(tree->left);
    struct sum_data *rightData = start_sum_thread(tree->right);
    int sumLeft = join_sum_thread(leftData);
    int sumRight = join_sum_thread(rightData);
    int f = fac(tree->value);
    //@ leak tree->left |-> _ &*& tree->right |-> _ &*& tree->value |-> _ &*& malloc_block_tree(tree);
    printf("%i", sumLeft + sumRight + f);
    return 0;
}