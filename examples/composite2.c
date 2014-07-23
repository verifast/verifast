#include "malloc.h"
#include <stdbool.h>

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate subtree(struct node *root, struct node *parent, int count)
    requires
        root == 0 ?
            count == 0
        :
            root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> count &*& malloc_block_node(root) &*&
            subtree(left, root, ?leftCount) &*& subtree(right, root, ?rightCount) &*& count == 1 + leftCount + rightCount;

predicate context(struct node *node, struct node *parent, int count)
    requires
        parent == 0 ?
            emp
        :
            parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*& malloc_block_node(parent) &*&
            context(parent, grandparent, parentCount) &*&
            (node == left ? 
                 subtree(right, parent, ?rightCount) &*& parentCount == 1 + count + rightCount
             :
                 node == right &*& subtree(left, parent, ?leftCount) &*& parentCount == 1 + count + leftCount
            );

predicate tree(struct node *node)
    requires context(node, ?parent, ?count) &*& subtree(node, parent, count);

@*/

void abort();
    //@ requires true;
    //@ ensures false;

struct node *create_tree()
    //@ requires emp;
    //@ ensures tree(result);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    //@ close subtree(0, n, 0);
    n->right = 0;
    //@ close subtree(0, n, 0);
    n->parent = 0;
    n->count = 1;
    //@ close subtree(n, 0, 1);
    //@ close context(n, 0, 1);
    //@ close tree(n);
    return n;
}

int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?count);
    //@ ensures subtree(node, parent, count) &*& result == count;
{
    int result = 0;
    //@ open subtree(node, parent, count);
    if (node == 0) {
    } else {
        result = node->count;
    }
    //@ close subtree(node, parent, count);
    return result;
}

int tree_get_count(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    //@ open tree(node);
    int result = subtree_get_count(node);
    //@ close tree(node);
    return result;
}

void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, _);
    //@ ensures context(node, parent, count);
{
    //@ open context(node, parent, _);
    if (parent == 0) {
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left) {
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else {
            leftCount = subtree_get_count(left);
            rightCount = count;
        }
        {
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }
    //@ close context(node, parent, count);
}

struct node *tree_add_left(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    //@ open tree(node);
    if (node == 0) {
        abort();
    }
    {
        struct node *n = malloc(sizeof(struct node));
        if (n == 0) {
            abort();
        }
        n->left = 0;
        //@ close subtree(0, n, 0);
        n->right = 0;
        //@ close subtree(0, n, 0);
        n->parent = node;
        n->count = 1;
        //@ close subtree(n, node, 1);
        //@ open subtree(node, ?parent, ?count);
        {
            struct node *nodeLeft = node->left;
            if (nodeLeft != 0) {
                abort();
            }
            //@ open subtree(nodeLeft, node, _);
            node->left = n;
            //@ close context(n, node, 0);
            fixup_ancestors(n, node, 1);
        }
        //@ close tree(n);
        return n;
    }
}

struct node *tree_add_right(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    //@ open tree(node);
    if (node == 0) {
        abort();
    }
    {
        struct node *n = malloc(sizeof(struct node));
        if (n == 0) {
            abort();
        }
        n->left = 0;
        //@ close subtree(0, n, 0);
        n->right = 0;
        //@ close subtree(0, n, 0);
        n->parent = node;
        n->count = 1;
        //@ close subtree(n, node, 1);
        //@ open subtree(node, ?parent, ?count);
        {
            struct node *nodeRight = node->right;
            if (nodeRight != 0) {
                abort();
            }
            //@ open subtree(nodeRight, node, _);
            node->right = n;
            //@ close context(n, node, 0);
            fixup_ancestors(n, node, 1);
        }
        //@ close tree(n);
        return n;
    }
}

struct node *tree_get_parent(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    if (node == 0) {
        abort();
    }
    {
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        //@ close subtree(node, parent, count);
        //@ open context(node, parent, count);
        //@ assert context(parent, ?grandparent, ?parentCount);
        //@ close subtree(parent, grandparent, parentCount);
        //@ close tree(parent);
        return parent;
    }
}

struct node *tree_get_left(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    if (node == 0) {
        abort();
    }
    {
        struct node *left = node->left;
        //@ assert subtree(left, node, ?leftCount);
        //@ close context(left, node, leftCount);
        //@ close tree(left);
        return left;
    }
}

struct node *tree_get_right(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(result);
{
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    if (node == 0) {
        abort();
    }
    {
        struct node *right = node->right;
        //@ struct node *left = node->left;
        //@ open subtree(left, node, ?leftCount);
        //@ open subtree(right, node, ?rightCount);
        //@ close subtree(left, node, leftCount);
        //@ close subtree(right, node, rightCount);
        //@ close context(right, node, rightCount);
        //@ close tree(right);
        return right;
    }
}

bool tree_has_parent(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    bool result = false;
    if (node == 0) {
    } else {
        struct node *parent = node->parent;
        result = parent != 0;
    }
    //@ close subtree(node, parent, count);
    //@ close tree(node);
    return result;
}

bool tree_has_left(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    bool result = false;
    if (node == 0) {
    } else {
        struct node *left = node->left;
        result = left != 0;
    }
    //@ close subtree(node, parent, count);
    //@ close tree(node);
    return result;
}

bool tree_has_right(struct node *node)
    //@ requires tree(node);
    //@ ensures tree(node);
{
    //@ open tree(node);
    //@ open subtree(node, ?parent, ?count);
    bool result = false;
    if (node == 0) {
    } else {
        struct node *right = node->right;
        result = right != 0;
    }
    //@ close subtree(node, parent, count);
    //@ close tree(node);
    return result;
}

void dispose_node(struct node *node)
    //@ requires subtree(node, _, _);
    //@ ensures emp;
{
    //@ open subtree(node, _, _);
    if (node == 0) {
    } else {
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}

void tree_dispose(struct node *node)
    //@ requires tree(node);
    //@ ensures emp;
{
    if (node == 0) {
        abort();
    }
    //@ open tree(node);
    //@ open context(node, ?parent, ?count);
    //@ open subtree(node, parent, count);
    {
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
        //@ close subtree(node, parent, count);
    }
    dispose_node(node);
}

int main()
    //@ requires emp;
    //@ ensures emp;
{
    struct node *node = create_tree();
    node = tree_add_left(node);
    node = tree_add_right(node);
    node = tree_get_parent(node);
    node = tree_add_left(node);
    node = tree_get_parent(node);
    node = tree_get_parent(node);
    tree_dispose(node);
    return 0;
}
