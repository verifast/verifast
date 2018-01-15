/*
  This libraries provides permission authfull(gid,n), owning the global, authoritative state of the ghost resource id gid, and some permissions authfrag(gid,m), owning fragments of gid 
  together with the knowledge that their fragments are all contained within the authoritative state.
  For more details, please take a look at 'Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning'.
*/

#ifndef AUTH_MONOID_H
#define AUTH_MONOID_H

/*
  A ghost linked listed is used to prove some desired lemmas related to the authoritative state of a ghost resource.
*/

struct g_node{
  //@ int value;
  //@ struct g_node *next;
};

/*@
predicate g_nodes(struct g_node* g_node; int n) =
  g_node == 0 ? n == 0 :
  [1/2]g_node->value |-> ?value &*&
  value >= 0 &*&
  [_]g_node->next |-> ?next &*&
  g_nodes(next,?m) &*&
  n == value + m;
  
predicate reaches(struct g_node *g_node1, struct g_node *g_node2) =
  g_node1 != 0 &*& g_node1 == g_node2 ? true :
  [_]g_node1->next |-> ?next &*&
  reaches(next,g_node2);
  
predicate one_g_node(struct g_node *g_node, struct g_node *g_node1, int value) =
  malloc_block_g_node(g_node1) &*&
  [1/2]g_node1->value |-> value &*&
  reaches(g_node,g_node1);
@*/

/*@
lemma struct g_node* create_g_node();
  requires true;
  ensures malloc_block_g_node(result) &*& result->value |-> _ &*& result->next |-> 0 &*& result != 0;

lemma void g_val_nat(struct g_node *g_node)
  requires g_nodes(g_node,?n);
  ensures g_nodes(g_node,n) &*& n >=0;
{
  open g_nodes(g_node,n);
  if (g_node != 0){
    g_val_nat(g_node->next);
  }
}

lemma void upd_g_node(struct g_node *g_node, int k)
  requires g_nodes(g_node,?n) &*& one_g_node(g_node,?g_node1,?m) &*& m+k>=0;
  ensures g_nodes(g_node,n+k) &*& one_g_node(g_node,g_node1,m+k) &*& n+k>=0;
{
  open one_g_node(g_node,g_node1,m);
  open reaches(g_node,g_node1);
  close reaches(g_node,g_node1);  
  open g_nodes(g_node,n);
  if (g_node == g_node1){
    g_node->value = m+k;
    close g_nodes(g_node,n+k);
    close one_g_node(g_node,g_node1,m+k);
    g_val_nat(g_node);
  }
  else{
    open reaches(g_node,g_node1);
    close one_g_node(g_node->next,g_node1,m);
    upd_g_node(g_node->next,k);
    open one_g_node(g_node->next,g_node1,m+k);
    assert [_]g_node->next |-> ?next;
    close reaches(g_node,g_node1);
    close one_g_node(g_node,g_node1,m+k);
    close g_nodes(g_node,n+k);
  }
}
@*/


/*
  The authoritative monoid
*/

/*@
predicate authfull(int gid, int n) =
  g_nodes((void*)gid, n);

predicate authfrag(int gid, int n) =
  one_g_node((void*) gid, _, n);

lemma int ghost_create1(int n)
  requires n>=0;
  ensures authfull(result, n) &*& authfrag(result, n);
{
  struct g_node *g_node= create_g_node();
  g_node->value = n;
  leak g_node->next |-> _;
  close g_nodes(g_node,n);
  close authfull((int)g_node,n);
  close reaches(g_node,g_node);
  close one_g_node(g_node,g_node,n);
  close authfrag((int)g_node,n);
  return (int)g_node;
}

lemma int ghost_create2(int n, int m)
  requires n>=0 &*& m>=0;
  ensures authfull(result, n+m) &*& authfrag(result, n) &*& authfrag(result, m);
{
  struct g_node *g_node= create_g_node();
  g_node->value = n;
  g_node->next = create_g_node();
  g_node->next->value = m;
  leak g_node->next |-> ?next;
  leak next->next |-> _;  
  close g_nodes(g_node->next,m);
  close g_nodes(g_node,n+m);
  close authfull((int)g_node,n+m);
  close reaches(g_node->next,g_node->next);
  close reaches(g_node,g_node->next);
  close one_g_node(g_node,g_node->next,m);
  close authfrag((int)g_node,m);
  close reaches(g_node,g_node);
  close one_g_node(g_node,g_node,n);
  close authfrag((int)g_node,n);
  return (int)g_node;
}

lemma void upd_ghost(int gid,int k)
  requires authfull(gid,?n) &*& authfrag(gid,?m) &*& m+k >= 0;
  ensures authfull(gid,n+k) &*& authfrag(gid,m+k) &*& n+k >= 0;
{
  open authfull(gid,n);
  open authfrag(gid,m);
  upd_g_node((void *)gid,k);
  close authfull(gid,n+k);
  close authfrag(gid,m+k);
}

lemma void ghost_split(int gid, int n, int m);
  requires authfrag(gid, n+m) &*& n>=0 &*& m>=0;
  ensures authfrag(gid, n) &*& authfrag(gid, m);
@*/

#endif