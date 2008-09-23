struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate tree(struct node *root, struct node *parent, int count)
    requires
        root == 0 ?
            count == 0
        :
            root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> count &*& malloc_block_node(root) &*&
            tree(left, root, ?leftCount) &*& tree(right, root, ?rightCount) &*& count == 1 + leftCount + rightCount;

predicate context(struct node *node, struct node *parent, int count)
    requires
        parent == 0 ?
            emp
        :
            parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*& malloc_block_node(parent) &*&
            context(parent, grandparent, parentCount) &*&
            (node == left ? 
                 tree(right, parent, ?rightCount) &*& parentCount == 1 + count + rightCount
             :
                 node == right &*& tree(left, parent, ?leftCount) &*& parentCount == 1 + count + leftCount
            );

@*/

int main()
    //@ requires emp;
    //@ ensures emp;
{
    struct node *root = create_tree();
    struct node *left = tree_add_left(root);
    struct node *leftLeft = tree_add_left(left);
    struct node *leftLeftLeft = tree_add_left(leftLeft);
    struct node *leftLeftLeftParent = tree_get_parent(leftLeftLeft);
    struct node *leftLeftLeftParentParent = tree_get_parent(leftLeftLeftParent);
    struct node *leftLeftLeftParentParentParent = tree_get_parent(leftLeftLeftParentParent);
    tree_dispose(leftLeftLeftParentParentParent);
    return 0;
}

struct node *create_tree()
    //@ requires emp;
    //@ ensures context(result, 0, 1) &*& tree(result, 0, 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    //@ close tree(0, n, 0);
    n->right = 0;
    //@ close tree(0, n, 0);
    n->parent = 0;
    n->count = 1;
    //@ close tree(n, 0, 1);
    //@ close context(n, 0, 1);
    return n;
}

void abort();
    //@ requires true;
    //@ ensures false;

struct node *tree_add_left(struct node *node)
    //@ requires context(node, ?parent, ?count) &*& tree(node, parent, count);
    //@ ensures context(result, node, 1) &*& tree(result, node, 1);
{
    if (node == 0) {
        abort();
    }
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
    //@ close tree(0, n, 0);
    n->right = 0;
    //@ close tree(0, n, 0);
    n->parent = node;
    n->count = 1;
    //@ close tree(n, node, 1);
    //@ open tree(node, parent, count);
    struct node *nodeLeft = node->left;
    if (nodeLeft != 0) {
        abort();
    }
    //@ open tree(nodeLeft, node, _);
    node->left = n;
    //@ close context(n, node, 0);
    fixup_ancestors(n, node, 1);
    return n;
}

int tree_get_count(struct node *node)
    //@ requires tree(node, ?parent, ?count);
    //@ ensures tree(node, parent, count) &*& result == count;
{
    int result = 0;
    //@ open tree(node, parent, count);
    if (node == 0) {
    } else {
        result = node->count;
    }
    //@ close tree(node, parent, count);
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
            rightCount = tree_get_count(right);
        } else {
            leftCount = tree_get_count(left);
            rightCount = count;
        }
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        fixup_ancestors(parent, grandparent, parentCount);
    }
    //@ close context(node, parent, count);
}

struct node *tree_get_parent(struct node *node)
    //@ requires context(node, ?parent, ?count) &*& tree(node, parent, count);
    //@ ensures context(parent, ?grandparent, ?parentCount) &*& tree(parent, grandparent, parentCount) &*& result == parent;
{
    //@ open tree(node, parent, count);
    if (node == 0) {
        abort();
    }
    struct node *parent = node->parent;
    if (parent == 0) {
        abort();
    }
    //@ close tree(node, parent, count);
    //@ open context(node, parent, count);
    //@ assert context(parent, ?grandparent, ?parentCount);
    //@ close tree(parent, grandparent, parentCount);
    return parent;
}

void tree_dispose(struct node *node)
    //@ requires context(node, ?parent, _) &*& tree(node, parent, _);
    //@ ensures emp;
{
    if (node == 0) {
        abort();
    }
    //@ open context(node, parent, _);
    //@ open tree(node, parent, ?count);
    struct node *parent = node->parent;
    if (parent != 0) {
        abort();
    }
    //@ close tree(node, parent, count);
    dispose_node(node);
}


void dispose_node(struct node *node)
    //@ requires tree(node, _, _);
    //@ ensures emp;
{
    //@ open tree(node, _, _);
    if (node == 0) {
    } else {
        struct node *left = node->left;
        dispose_node(left);
        struct node *right = node->right;
        dispose_node(right);
        free(node);
    }
}
