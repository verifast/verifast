#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@

inductive tree =
    empty
  | tree(struct node *, tree, tree);

fixpoint int tcount(tree nodes) {
  switch (nodes) {
    case empty: return 0;
    case tree(root, left, right):
      return 1 + tcount(left) + tcount(right);
  }
}

lemma void tcount_nonnegative(tree nodes)
  requires true;
  ensures 0 <= tcount(nodes);
{
  switch (nodes) {
    case empty:
    case tree(n, l, r):
      tcount_nonnegative(l);
      tcount_nonnegative(r);
  }
}

predicate subtree(struct node * root, struct node * parent, tree t) =
  switch (t) {
    case empty: return root == 0;
    case tree(root0, leftNodes, rightNodes):
      return
        root == root0 &*& root != 0 &*&
        root->left |-> ?left &*&
        root->right |-> ?right &*&
        root->parent |-> parent &*&
        root->count |-> tcount(t) &*&
        malloc_block_node(root) &*&
        subtree(left, root, leftNodes) &*&
        subtree(right, root, rightNodes);
  };

inductive context =
    root
  | left_context(context, struct node *, tree)
  | right_context(context, struct node *, tree);

predicate context(struct node * node, struct node * parent,
                  int count, context nodes) =
  switch (nodes) {
    case root: return parent == 0;
    case left_context(pns, parent0, rightNodes):
      return
        parent == parent0 &*& parent != 0 &*&
        parent->left |-> node &*&
        parent->right |-> ?right &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        malloc_block_node(parent) &*&
        context(parent, gp, pcount, pns) &*&
        subtree(right, parent, rightNodes) &*&
        pcount == 1 + count + tcount(rightNodes);
    case right_context(pns, parent0, leftNodes):
      return
        parent == parent0 &*& parent != 0 &*&
        parent->left |-> ?left &*&
        parent->right |-> node &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        malloc_block_node(parent) &*&
        context(parent, gp, pcount, pns) &*&
        subtree(left, parent, leftNodes) &*&
        pcount == 1 + tcount(leftNodes) + count;
  };

predicate tree(struct node * node, context c, tree subtree) =
  context(node, ?parent, tcount(subtree), c) &*&
  subtree(node, parent, subtree);

@*/

struct node * create_node(struct node * p)
  //@ requires emp;
  /*@ ensures 
       subtree(result, p, tree(result, empty, empty));
  @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; //@ close subtree(0, n, empty);
  n->right = 0; //@ close subtree(0, n, empty);
  n->parent = p;
  n->count = 1;
  //@ close subtree(n, p, tree(n, empty, empty));
  return n;
}

struct node *create_tree()
  //@ requires emp;
  /*@ ensures
       tree(result, root, tree(result, empty, empty));
  @*/
{
  struct node *n = create_node(0);
  //@ close context(n, 0, 1, root);
  //@ close tree(n, root, tree(n, empty, empty));
  return n;
}

int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?parent, ?nodes);
  /*@ ensures subtree(node, parent, nodes) &*&
              result == tcount(nodes) &*& 0 <= result; @*/
{
  int result = 0;
  //@ open subtree(node, parent, nodes);
  if (node != 0) { result = node->count; }
  //@ close subtree(node, parent, nodes);
  //@ tcount_nonnegative(nodes);
  return result;
}

void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires context(n, p, _, ?c) &*& 0 <= count &*& n->left |-> ?nLeft;
  //@ ensures context(n, p, count, c) &*& n->left |-> nLeft;
{
  //@ open context(n, p, _, c);
  if (p == 0) {
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      //@ if (n != left) { open subtree(left, _, _); pointer_fractions_same_address(&n->left, &left->left); }
      leftCount = count;
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
    }
  }
  //@ close context(n, p, count, c);
}

struct node *tree_add_left(struct node *node)
  /*@ requires
        tree(node, ?c, ?t) &*&
        switch (t) {
          case empty: return false;
          case tree(n0, l, r): return l == empty;
        }; @*/
  /*@ ensures
        switch (t) {
          case empty: return false;
          case tree(n0, l, r): return
            tree(result, left_context(c, node, r),
              tree(result, empty, empty));
        };
  @*/
{
  //@ open tree(node, c, t);
  struct node *n = create_node(node);
  //@ open subtree(node, ?parent, t);
  //@ struct node *nodeRight = node->right;
  //@ assert subtree(nodeRight, node, ?r);
  {
      struct node *nodeLeft = node->left;
      //@ open subtree(nodeLeft, node, empty);
      node->left = n;
      /*@ close context(n, node, 0,
                  left_context(c, node, r)); @*/
      //@ open subtree(n, node, tree(n, empty, empty));
      fixup_ancestors(n, node, 1);
      //@ close subtree(n, node, tree(n, empty, empty));
  }
  /*@ close tree(n, left_context(c, node, r),
              tree(n, empty, empty)); @*/
  return n;
}

struct node *tree_add_right(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return rightNodes == empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, right_context(contextNodes, node, leftNodes), tree(result, empty, empty));
            };
    @*/
{
    //@ open tree(node, contextNodes, subtreeNodes);
    struct node *n = create_node(node);
    //@ open subtree(node, ?parent, subtreeNodes);
    //@ struct node *nodeLeft = node->left;
    //@ assert subtree(nodeLeft, node, ?leftNodes);
    {
        struct node *nodeRight = node->right;
        //@ open subtree(nodeRight, node, empty);
        node->right = n;
        //@ close context(n, node, 0, right_context(contextNodes, node, leftNodes));
        //@ open subtree(n, node, tree(n, empty, empty));
        fixup_ancestors(n, node, 1);
        //@ close subtree(n, node, tree(n, empty, empty));
    }
    //@ close tree(n, right_context(contextNodes, node, leftNodes), tree(n, empty, empty));
    return n;
}

struct node *tree_get_parent(struct node *node)
  /*@ requires tree(node, ?c, ?t) &*&
        c != root &*& t != empty; @*/
  /*@ ensures
        switch (c) {
          case root: return false;
          case left_context(pns, p, r):
            return result == p &*&
              tree(p, pns, tree(p, t, r));
          case right_context(pns, p, l):
            return result == p &*&
              tree(p, pns, tree(p, l, t));
        }; @*/
{
  //@ open tree(node, c, t);
  //@ open subtree(node, _, t);
  struct node *p = node->parent;
  //@ close subtree(node, p, t);
  //@ open context(node, p, tcount(t), c);
  //@ assert context(p, ?gp, ?pcount, ?pns);
  /*@ switch (c) {
        case root:
        case left_context(pns0, p0, r):
            close subtree(p, gp, tree(p, t, r));
        case right_context(pns0, p0, l):
            close subtree(p, gp, tree(p, l, t));
      }
  @*/
  //@ assert subtree(p, gp, ?pt);
  //@ close tree(p, pns, pt);
  return p;
}

void subtree_dispose(struct node *node)
  //@ requires subtree(node, _, _);
  //@ ensures emp;
{
  //@ open subtree(node, _, _);
  if (node != 0) {
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
  }
}

void tree_dispose(struct node *node)
  //@ requires tree(node, root, _);
  //@ ensures emp;
{
  //@ open tree(node, root, _);
  //@ open context(node, _, _, root);
  subtree_dispose(node);
}

int main0()
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

/*@

fixpoint tree combine(context c, tree t) {
    switch (c) {
        case root: return t;
        case left_context(pns, p, right):
          return combine(pns, tree(p, t, right));
        case right_context(pns, p, left):
          return combine(pns, tree(p, left, t));
    }
}

inductive path = here | left(path) | right(path);

fixpoint bool contains_at_path(tree nodes, path path, struct node *node) {
    switch (nodes) {
        case empty: return false;
        case tree(rootNode, leftNodes, rightNodes):
            return
                switch (path) {
                    case here: return node == rootNode;
                    case left(path0): return contains_at_path(leftNodes, path0, node);
                    case right(path0): return contains_at_path(rightNodes, path0, node);
                };
    }
}

lemma void go_to_root(context contextNodes)
    requires tree(?node, contextNodes, ?subtreeNodes);
    ensures tree(?rootNode, root, combine(contextNodes, subtreeNodes));
{
    switch (contextNodes) {
        case root:
        case left_context(parentContextNodes, parent, rightNodes):
            open tree(node, contextNodes, subtreeNodes);
            open context(node, _, _, _);
            assert context(parent, ?grandparent, _, _);
            close subtree(parent, grandparent, tree(parent, subtreeNodes, rightNodes));
            close tree(parent, parentContextNodes, tree(parent, subtreeNodes, rightNodes));
            go_to_root(parentContextNodes);
        case right_context(parentContextNodes, parent, leftNodes):
            open tree(node, contextNodes, subtreeNodes);
            open context(node, _, _, _);
            assert context(parent, ?grandparent, _, _);
            close subtree(parent, grandparent, tree(parent, leftNodes, subtreeNodes));
            close tree(parent, parentContextNodes, tree(parent, leftNodes, subtreeNodes));
            go_to_root(parentContextNodes);
    }
}

fixpoint path combine_path(context contextNodes, path path) {
    switch (contextNodes) {
        case root: return path;
        case left_context(parentContextNodes, parent, rightNodes): return combine_path(parentContextNodes, left(path));
        case right_context(parentContextNodes, parent, leftNodes): return combine_path(parentContextNodes, right(path));
    }
}

fixpoint context get_context_nodes_at_path(context contextNodes, tree subtreeNodes, path path) {
    switch (path) {
        case here: return contextNodes;
        case left(path0):
            return
                switch (subtreeNodes) {
                    case empty: return contextNodes;
                    case tree(rootNode, leftNodes, rightNodes):
                        return get_context_nodes_at_path(left_context(contextNodes, rootNode, rightNodes), leftNodes, path0);
                };
        case right(path0):
            return
                switch (subtreeNodes) {
                    case empty: return contextNodes;
                    case tree(rootNode, leftNodes, rightNodes):
                        return get_context_nodes_at_path(right_context(contextNodes, rootNode, leftNodes), rightNodes, path0);
                };
    }
}

fixpoint tree get_subtree_nodes_at_path(tree subtreeNodes, path path) {
    switch (subtreeNodes) {
        case empty: return empty;
        case tree(rootNode, leftNodes, rightNodes):
            return
                switch (path) {
                    case here: return subtreeNodes;
                    case left(path0): return get_subtree_nodes_at_path(leftNodes, path0);
                    case right(path0): return get_subtree_nodes_at_path(rightNodes, path0);
                };
    }
}

lemma void go_to_descendant(struct node *node0, path path, struct node *node)
    requires tree(node0, ?contextNodes, ?subtreeNodes) &*& contains_at_path(subtreeNodes, path, node) == true;
    ensures tree(node, get_context_nodes_at_path(contextNodes, subtreeNodes, path), get_subtree_nodes_at_path(subtreeNodes, path));
{
    switch (path) {
        case here:
            open tree(node0, contextNodes, subtreeNodes);
            open subtree(node0, ?parent, subtreeNodes);
            switch (subtreeNodes) {
                case empty:
                case tree(node00, leftNodes, rightNodes):
                    close subtree(node0, parent, subtreeNodes);
                    close tree(node0, contextNodes, subtreeNodes);
            }
        case left(path0):
            open tree(node0, contextNodes, subtreeNodes);
            open subtree(node0, ?parent, subtreeNodes);
            switch (subtreeNodes) {
                case empty:
                case tree(node00, leftNodes, rightNodes):
                    struct node *left = node0->left;
                    close context(left, node0, tcount(leftNodes), left_context(contextNodes, node0, rightNodes));
                    close tree(left, left_context(contextNodes, node0, rightNodes), leftNodes);
                    go_to_descendant(left, path0, node);
            }
        case right(path0):
            open tree(node0, contextNodes, subtreeNodes);
            open subtree(node0, ?parent, subtreeNodes);
            switch (subtreeNodes) {
                case empty:
                case tree(node00, leftNodes, rightNodes):
                    struct node *right = node0->right;
                    close context(right, node0, tcount(rightNodes), right_context(contextNodes, node0, leftNodes));
                    close tree(right, right_context(contextNodes, node0, leftNodes), rightNodes);
                    go_to_descendant(right, path0, node);
            }
    }
}

lemma void change_focus(struct node *node0, path path, struct node *node)
    requires tree(node0, ?contextNodes, ?subtreeNodes) &*& contains_at_path(combine(contextNodes, subtreeNodes), path, node) == true;
    ensures tree(node, get_context_nodes_at_path(root, combine(contextNodes, subtreeNodes), path), get_subtree_nodes_at_path(combine(contextNodes, subtreeNodes), path));
{
    go_to_root(contextNodes);
    assert tree(?rootNode, _, _);
    go_to_descendant(rootNode, path, node);
}

@*/

int main() //@ : main
    //@ requires emp;
    //@ ensures emp;
{
    struct node *root = create_tree();
    struct node *left = tree_add_left(root);
    struct node *leftRight = tree_add_right(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    //@ assert leftRightParent == left;
    struct node *leftLeft = tree_add_left(left);
    //@ change_focus(leftLeft, left(right(here)), leftRight);
    struct node *leftRightRight = tree_add_right(leftRight);
    //@ change_focus(leftRightRight, left(left(here)), leftLeft);
    //@ change_focus(leftLeft, here, root);
    tree_dispose(root);
    return 0;
}
