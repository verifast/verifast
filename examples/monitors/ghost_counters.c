//@ #include "ghost_cells.gh"
//@ #include "ghost_counters.gh"

/*@
inductive node = empty | node(int value_id, int is_last_id, int next_id);

predicate node(int node_id, int value_id, int is_last_id, int next_id; int value, bool is_last, node next) =
  ghost_cell<node> (node_id, node(value_id, is_last_id, next_id)) &*&
  ghost_cell<int> (value_id, value) &*&
  ghost_cell<bool> (is_last_id, is_last) &*&
  ghost_cell<node> (next_id, next);

predicate nodes(int node_id; int n) =
  [_]ghost_cell<node> (node_id, node(?value_id, ?is_last_id, ?next_id)) &*&
  [1/2]ghost_cell<int> (value_id, ?value) &*&
  ghost_cell<bool> (is_last_id, ?is_last) &*&
  value >= 0 &*&
  is_last == true ? 
  ghost_cell<node> (next_id, empty) &*&
  n == value :
  nodes(next_id,?m) &*&
  n == value + m;

predicate reaches(int node1_id, int node2_id) =
  node1_id == node2_id ? true :
  [_]ghost_cell<node> (node1_id, node(?value_id, ?is_last_id, ?next_id)) &*&
  reaches(next_id,node2_id);  
 
predicate one_node(int node_id, int node1_id, int value) =
  [_]ghost_cell<node> (node1_id, node(?value_id, ?is_last_id, ?next_id)) &*&  
  [1/2]ghost_cell<int> (value_id, value) &*&
  value >= 0 &*&
  reaches(node_id,node1_id); 

lemma int create_node()
  requires true;
  ensures ghost_cell<node> (result, node(?value_id, ?is_last_id, ?next_id)) &*&  
          ghost_cell<int> (value_id, 0) &*&
          ghost_cell<bool> (is_last_id, true) &*&
          ghost_cell<node> (next_id, empty);
{
    int value_id = create_ghost_cell<int>(0);
    int is_last_id = create_ghost_cell<bool>(true);
    int next_id = create_ghost_cell<node>(empty);
    return create_ghost_cell<node>(node(value_id, is_last_id, next_id));
}

lemma void g_val_nat(int node_id)
  requires nodes(node_id,?n);
  ensures nodes(node_id,n) &*& n >=0;
{
  open nodes(node_id, n);
  assert [_]ghost_cell<node> (node_id, node(?value_id, ?is_last_id, ?next_id));
  assert [_]ghost_cell<bool> (is_last_id, ?is_last);
  if (!is_last) {
    g_val_nat(next_id);
  }
}

lemma void foo0()
  requires ghost_cell<node> (?id1,_) &*& [_]ghost_cell<node> (id1,_);
  ensures false;
{
    ghost_cell_fraction_info(id1);
}

lemma void foo(int id1, int id2)
  requires ghost_cell<node> (id1,?node1) &*& [_]ghost_cell<node> (id2,?node2);
  ensures ghost_cell<node> (id1,node1) &*& [_]ghost_cell<node> (id2,node2) &*& id1 != id2;
{
    if (id1 == id2) foo0();
}

lemma void foo1(int id)
  requires ghost_cell<node> (id,empty) &*& [_]ghost_cell<node> (id,node(?value1_id, ?is_last1_id, ?next1_id));
  ensures false;{}

lemma void dec_node(int node_id)
  requires nodes(node_id,?n) &*& one_node(node_id,?node1_id,?k) &*& n+k >= 0;
  ensures nodes(node_id,n-k) &*& one_node(node_id,node1_id,0) &*& n-k >= 0;
{
  open one_node(node_id,node1_id,k);
  open reaches(node_id,node1_id);
  close reaches(node_id,node1_id);  
  open nodes(node_id,n);
  assert [_]ghost_cell<node> (node_id, node(?value_id, ?is_last_id, ?next_id));
  if (node_id == node1_id){
    ghost_cell_mutate(value_id, 0); 
    close nodes(node_id,n-k);
    close one_node(node_id,node1_id,0);
    g_val_nat(node_id);
  }
  else{
    open reaches(node_id,node1_id);
    open reaches(next_id,node1_id);
    close reaches(next_id,node1_id);
    assert [_]ghost_cell<node> (node1_id, ?node1);
    if (node1 == empty){
      foo1(node1_id);
    }
    assert [_]ghost_cell<bool> (is_last_id, ?is_last);    
    if (!is_last) {    
      close one_node(next_id,node1_id,k);
      assert nodes(next_id, ?m);
      if (m<0){
        g_val_nat(next_id);
      }
      dec_node(next_id);   
      open one_node(next_id, node1_id, 0); 
      close reaches(node_id, node1_id);
      close one_node(node_id, node1_id, 0);
    }
  }
}

lemma void inc_node(int node_id, int k)
  requires nodes(node_id,?n) &*& k>=0;
  ensures nodes(node_id,n+k) &*& one_node(node_id,?node1_id,k);// &*& node1_id != node_id;
{
  open nodes(node_id,n);
  assert [?f]ghost_cell<node> (node_id, node(?value_id, ?is_last_id, ?next_id));
  assert ghost_cell<bool> (is_last_id, ?is_last);
  if (is_last){
    int value1_id = create_ghost_cell<int>(k);
    int is_last1_id = create_ghost_cell<bool>(true);
    int next1_id = create_ghost_cell<node>(empty);
    ghost_cell_mutate(is_last_id, false);
    ghost_cell_mutate(next_id, node(value1_id, is_last1_id, next1_id));
    foo(next_id, node_id);
    leak [_]ghost_cell<node>(next_id, node(value1_id, is_last1_id, next1_id));
    close nodes(next_id, k);  
    close nodes(node_id,n+k);
    close reaches(next_id, next_id);
    close reaches(node_id, next_id);    
    close one_node(node_id, next_id, k);
  }
  else{
    inc_node(next_id,k);
    open one_node(next_id,?node1_id,k);
    close reaches(node_id,node1_id);
    close one_node(node_id,node1_id,k);
    assert [?f1]ghost_cell<node> (node1_id, node(?value1_id, ?is_last1_id, ?next1_id));
    if (node_id == node1_id){
      if (node(value_id, is_last_id, next_id) != node(value1_id, is_last1_id, next1_id))
          ghost_cell_fraction_info(node_id);
      leak reaches(next_id, node1_id);      
    }
    close nodes(node_id,n+k);
  }
}
@*/

/*@
predicate ctr(int id; int n) =
  nodes(id,n);

predicate tic(int id) =
  one_node(id,_,1);

lemma int new_ctr()
  requires true;
  ensures ctr(result, 0);
{
  int node_id = create_node();
  leak ghost_cell<node> (node_id,_);
  close nodes(node_id,0);
  close ctr(node_id,0);
  close reaches(node_id, node_id);
  close one_node(node_id, node_id, 0);
  leak one_node(node_id, node_id, 0);
  return node_id;
}

lemma void inc_ctr(int id)
  requires ctr(id,?n);
  ensures ctr(id,n+1) &*& tic(id);
{
  open ctr(id,n);
  inc_node(id,1);
  close ctr(id,n+1);
  close tic(id);
}

lemma void dec_ctr(int id)
  requires ctr(id,?n) &*& tic(id);
  ensures ctr(id,n-1) &*& n>0;
{
  open ctr(id,n);
  open tic(id);
  g_val_nat(id);
  dec_node(id);
  close ctr(id,n-1);
  leak one_node(id,_,0);
}
@*/