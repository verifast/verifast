#ifndef PROPHECY_H
#define PROPHECY_H

#include <stdlib.h> // abort()

//@ predicate prophecy(int id, int prophetic_value);

// Note: don't simply use a lemma instead of a C function. With a lemma
// there would be an unsoundness, exploitable like this:
//  //@ assert prophecy(id, ?val); prophecy_assign(id, val+1); assert val == val+1;
void prophecy_assign(int id, int real_value);
//@ requires prophecy(id, ?prophetic_value);
//@ ensures real_value == prophetic_value;

int create_prophecy();
//@ requires true;
//@ ensures prophecy(result, _) &*& result != 0;

struct proph_tree {
  int id;
  struct proph_tree *left;
  struct proph_tree *right;
};
/*@
predicate proph_tree (struct proph_tree *tree, bool used, int c, struct proph_tree *left, struct proph_tree *right) =
  tree->id |-> ?id
  &*& (used ? prophecy(id, c) : emp)
  &*& tree->left |-> left
  &*& tree->right |-> right
  &*& malloc_block_proph_tree(tree);
@*/
struct proph_tree *create_proph_tree(bool used, struct proph_tree *left, struct proph_tree *right)
//@ requires true;
//@ ensures proph_tree(result, used, _, left, right);
{
  struct proph_tree *tree = malloc(sizeof(struct proph_tree));
  if (tree == 0){
    abort();
  }
  //@ int c = 0;
  if (used){
    tree->id = create_prophecy();
    //@ assert prophecy(_, ?new_c);
    //@ c = new_c;
  }else{
    tree->id = 0;
  }
  tree->left = left;
  tree->right = right;
  //@ close proph_tree(tree, used, c, left, right);
  return tree;
}


#endif
