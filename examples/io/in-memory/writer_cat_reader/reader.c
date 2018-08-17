#include "reader.h"

/** Reads four ints and returns the sum. */
int reader/*@<u> @*/(struct queue *queue, struct proph_tree *tree)
/*@ requires
  [?f_queue]queue(?queue_id, queue)
  &*& reader_io<u>(queue_id, ?t1, 4, ?read, ?t2, tree)
  &*& token(t1);
@*/
/*@ ensures
  [f_queue]queue(queue_id, queue)
  &*& token(t2)
  &*& result == fold_left(0, plus, read);
@*/
{
  int sum = 0;
  struct proph_tree *old_tree;
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(_, _, _, _, _);
  int c = getchar(queue, tree->left);
  sum = sum + c;
  old_tree = tree;
  tree = tree->right;
  free(old_tree);
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(_, _, _, _, _);
  c = getchar(queue, tree->left);
  sum = sum + c;
  old_tree = tree;
  tree = tree->right;
  free(old_tree);
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(_, _, _, _, _);
  c = getchar(queue, tree->left);
  sum = sum + c;
  old_tree = tree;
  tree = tree->right;
  free(old_tree);
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(_, _, _, _, _);
  c = getchar(queue, tree->left);
  sum = sum + c;
  
  free(tree);
  
  //@ open reader_io(_, _, _, _, _, _);
  return sum;
}