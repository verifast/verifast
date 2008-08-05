struct Node {
  struct Node* left;
	struct Node* right;
	struct Node* parent;
	int count;
};


/*@
inductive tree = | Nil | tree(struct Node*, tree, tree);

fixpoint int size(tree t) {
  switch(t) {
	  case Nil: return 0;
    case tree(node, lhs, rhs): return 1 + size(lhs) + size(rhs);
	}
}

inductive treeseg = | ltreeseg(struct Node*, treeseg, tree) | rtreeseg(struct Node*, tree, treeseg) | Hole(struct Node*);

predicate treeseg(struct Node* node, treeseg value, struct Node* parent, int holeCount)
  requires switch(value) {
		case ltreeseg(n, lhs, rhs): return n!=0 &*& n==node &*&  node->parent |-> parent &*& node->count |-> ?c &*& c == tssize(value, holeCount) &*&
		                                   node->left |-> ?l &*& node->right |-> ?r &*& (l!=0 &*& treeseg(l, lhs, node, holeCount)) &*&
																			 (r==0 ? rhs==Nil : tree(r, rhs, node)) &*& malloc_block_Node(node);  
		case rtreeseg(n, lhs, rhs): return n!=0 &*& n==node &*&  node->parent |-> parent &*& node->count |-> ?c &*& c == tssize(value, holeCount) &*&
		                                   node->left |-> ?l &*& node->right |-> ?r &*& (r!=0 &*& treeseg(r, rhs, node, holeCount)) &*&
																			 (l==0 ? lhs==Nil : tree(l, lhs, node)) &*& malloc_block_Node(node);  
    case Hole(n): return node == n;
	};

fixpoint int tssize(treeseg t, int holeCount) {
  switch(t) {
		case ltreeseg(n, lhs, rhs): return 1 + tssize(lhs, holeCount) + size(rhs);
		case rtreeseg(n, lhs, rhs): return 1 + size(lhs) + tssize(rhs, holeCount); 
    case Hole(n): return holeCount;
	}
}
  
predicate tree(struct Node* node, tree value, struct Node* parent)
  requires switch(value) { 
		case Nil: return false;
		case tree(node2, lhs, rhs): return node!=0 &*& node==node2 &*& node->parent |-> parent &*& node->count |-> ?c &*& c == size(value) &*&
		                                   node->left |-> ?l &*& node->right |-> ?r &*& (l==0 ? lhs==Nil : tree(l, lhs, node)) &*&
																			 (r==0 ? rhs==Nil : tree(r, rhs, node)) &*& malloc_block_Node(node); 
  };





inductive path = | NilPath | LeftCons(path) | RightCons(path);

inductive pathOption = | None | Some(path);

fixpoint pathOption findHelper2(pathOption po2) {
  switch(po2) {
	  case None: return None;
	  case Some(pa): return Some(RightCons(pa));
	}
}

fixpoint pathOption findHelper(pathOption po1, pathOption po2) {
  switch(po1) {
	  case None: return findHelper2(po2);
		case Some(pa): return Some(LeftCons(pa));
	}
}

fixpoint pathOption find(tree t, struct Node* n) {
  switch(t) {
	  case Nil: return None;
		case tree(r, lhs, rhs): return r==n ? Some(NilPath) : findHelper(find(lhs, n), find(rhs, n));
	}
}

fixpoint path the(pathOption pa) {
  switch(pa) {
	  case None: return NilPath;
		case Some(p): return p;
	}
}

fixpoint struct Node* thehole(treeseg ts) {
  switch(ts) {
		case ltreeseg(n, lhs, rhs): return thehole(lhs);
		case rtreeseg(n, lhs, rhs): return thehole(rhs);
		case Hole(n): return n;
	}
}

fixpoint struct Node* holeParent(treeseg ts, struct Node* myparent) {
	switch(ts) {
		case ltreeseg(n, lhs, rhs): return holeParent(lhs, n);
		case rtreeseg(n, lhs, rhs): return holeParent(rhs, n);
		case Hole(n): return myparent;
	}
}
@*/

struct Node* create(struct Node* parent)
  requires emp;
	ensures tree(result, tree(result, Nil, Nil), parent);
{
	struct Node* n = malloc(sizeof(struct Node));
	if(n==0) {
		abort();
	} else {}
	n->left = 0;
	n->right = 0;
	n->parent = parent;
	n->count = 1;
	//@ close tree(n, tree(n, Nil, Nil), parent); 
	return n;
}

struct Node* addLeftChild(struct Node* node)
  /*@ requires treeseg(?root, ?value, 0) &*& thehole(value) == node &*& node->left |-> 0 &*& node->right |-> 0 &*&
	             malloc_block_Node(node) &*& node->parent |-> holeParent(value, 0) &*& node->count |-> _; @*/
	//@ ensures tree(root, addChild(value, the(find(value, node)), result), 0); 
{
	  child = create(node);
		node->left = child;
		node->count = 2;
		struct Node* par = node->parent;
		//@ close tree(node, tree(node, tree(child, Nil, Nil), Nil), par);
    fix(par, node, 2);
}

void fix(struct Node* parent, struct Node* child)
  //@ 
	//@ ensures tree(root, addChild(value)
{
	abort();
}

void abort()
  requires emp;
	ensures false; 
{
	while(true)
	 //@ invariant emp;	
	{
	}
}
  