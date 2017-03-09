#include "cat.h"

/**
 * Reads four numbers from queue_from, and write that to queue_to.
 * Buffering is allowed.
 */
void cat/*@<u> @*/(struct queue *queue_from, struct queue *queue_to, struct proph_tree *tree)
/*@ requires
  [?f_queue_from]queue(?queue_id_from, queue_from)
  &*& [?f_queue_to]queue(?queue_id_to, queue_to)
  &*& cat_io<u>(queue_id_from, queue_id_to, ?t1, ?text, ?t2, tree)
  &*& token(t1);
@*/
/*@ ensures
  [f_queue_from]queue(queue_id_from, queue_from)
  &*& [f_queue_to]queue(queue_id_to, queue_to)
  &*& token(t2);
@*/
{
  //@ open cat_io(_, _, _, _, _, _);
  //@ split(t1);
  int c1;
  int c2;
  struct proph_tree *old_tree;
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(tree, _, _, _, _);
  c1 = getchar(queue_from, tree->left);
  old_tree = tree;
  tree = tree->right;
  free(old_tree);
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(tree, _, _, _, _);
  c2 = getchar(queue_from, tree->left);
  old_tree = tree;
  tree = tree->right;
  free(old_tree);
  
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c1);
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c2);
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(tree, _, _, _, _);
  c1 = getchar(queue_from, tree->left);
  old_tree = tree;
  tree = tree->right;
  free(old_tree);
  
  //@ open reader_io(_, _, _, _, _, _);
  //@ open proph_tree(tree, _, _, _, _);
  c2 = getchar(queue_from, tree->left);
  
  free(tree);
  
  //@ open reader_io(_, _, _, _, ?tr2, _);
  
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c1);
  //@ open writer_io(_, _, _, _);
  putchar(queue_to, c2);
  //@ open writer_io(_, _, _, _);
  //@ join(tr2);
}
