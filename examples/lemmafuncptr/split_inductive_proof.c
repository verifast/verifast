/*@

inductive tree =
  | node(tree child1, tree child2)
  | leaf
;

fixpoint int max(int i1, int i2)
{
  return i1 > i2 ? i1 : i2;
}

fixpoint int tree_height(tree t)
{
  switch (t)
  {
    case node(child1, child2):
      return 1 + max(tree_height(child1), tree_height(child2));
    case leaf:
      return 1;
  }
}

//Proof with induction in a single lemma
lemma void tree_height_is_positive_normal_recursion(tree t)
  requires true;
  ensures  tree_height(t) > 0;
{
  switch (t)
  {
    case node(child1, child2):
      tree_height_is_positive_normal_recursion(child1);
      tree_height_is_positive_normal_recursion(child2);
      assert tree_height(t) > 0;
    case leaf:
      assert tree_height(t) > 0;
  }
}

//Proof with induction where the inductive cases are split over multiple lemmas,
//comes in handy when proof in one single lemma becomes to slow
typedef lemma void split_proof(tree t);
  requires split_proof_container(t);
  ensures  split_proof_container(t) &*&
           tree_height(t) > 0;

predicate split_proof_container(tree t) =
  switch (t)
  {
    case node(child1, child2):
      return is_split_proof(_) &*&
             split_proof_container(child1) &*&
             split_proof_container(child2);
    case leaf:
      return true;
  }
;

//Inductive case for a node
lemma void node_height(tree t)
  requires split_proof_container(t) &*&
           t == node(?child1, ?child2);
  ensures  split_proof_container(t) &*&
           tree_height(t) > 0;
{
  open split_proof_container(t);
  assert is_split_proof(?proof);
  assert split_proof_container(child1);
  assert split_proof_container(child2);
  proof(child1);
  proof(child2);
  assert tree_height(t) > 0;
  close split_proof_container(t);
}

//Inductive case for a leaf
lemma void leaf_height(tree t)
  requires split_proof_container(t) &*& //Not necessary since this is not a recursive case
           t == leaf;
  ensures  split_proof_container(t) &*& //Not necessary since this is not a recursive case
           tree_height(t) > 0;
{
  assert tree_height(t) > 0;
}

//Combine the inductive cases in a single proof
lemma void split_proof_implementation(tree t) : split_proof
  requires split_proof_container(t);
  ensures  split_proof_container(t) &*&
           tree_height(t) > 0;
{
  switch (t)
  {
    case node(child1, child2):
     node_height(t);
    case leaf:
     leaf_height(t);
  }
}

lemma void produce_split_proof_container(tree t)
  nonghost_callers_only
  requires true;
  ensures  split_proof_container(t);
{
  switch (t)
  {
    case node(child1, child2):
     produce_split_proof_container(child1);
     produce_split_proof_container(child2);
     produce_lemma_function_pointer_chunk(split_proof_implementation)
     {
       duplicate_lemma_function_pointer_chunk(split_proof);
     }
     close split_proof_container(t);
    case leaf:
     close split_proof_container(t);
  }
}

lemma void tree_height_is_positive_split_recursion(tree t)
  nonghost_callers_only
  requires true;
  ensures  tree_height(t) > 0;
{
  produce_split_proof_container(t);
  switch (t)
  {
    case node(child1, child2):
     node_height(t);
    case leaf:
     leaf_height(t);
  }
  leak split_proof_container(t);
}

@*/