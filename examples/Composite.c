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

inductive context = | lcontext(struct Node*, context, tree) | rcontext(struct Node*, tree, context) | Root; 

predicate context(struct Node* node, context value, int holeCount)
  requires switch(value) {
    case Root: return node->parent |-> 0;
    case lcontext(n, cont, t): return n!=0 &*& n->left |-> node &*& n->right |-> ?r &*& n->count |-> ?c &*&
                                      (r==0 ? emp : tree(r, t) &*& r->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n &*&
                                      malloc_block_Node(n);
    case rcontext(n, t, cont): return n!=0 &*& n->right |-> node &*& n->left |-> ?l &*& n->count |-> ?c &*&
                                      (l==0 ? emp : tree(l, t) &*& l->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n &*&
                                      malloc_block_Node(n);
  };

predicate treeseg(struct Node* node, treeseg value, struct Node* parent, int holeCount)
  requires switch(value) {
    case ltreeseg(n, lhs, rhs): return n!=0 &*& n==node &*&  node->parent |-> parent &*& node->count |-> ?c &*& c == tssize(value, holeCount) &*&
                                       node->left |-> ?l &*& node->right |-> ?r &*& (l!=0 &*& treeseg(l, lhs, node, holeCount)) &*&
                                       (r==0 ? rhs==Nil : tree(r, rhs)) &*& malloc_block_Node(node);  
    case rtreeseg(n, lhs, rhs): return n!=0 &*& n==node &*&  node->parent |-> parent &*& node->count |-> ?c &*& c == tssize(value, holeCount) &*&
                                       node->left |-> ?l &*& node->right |-> ?r &*& (r!=0 &*& treeseg(r, rhs, node, holeCount)) &*&
                                       (l==0 ? lhs==Nil : tree(l, lhs)) &*& malloc_block_Node(node);  
    case Hole(n): return node == n;
  };

fixpoint int tssize(treeseg t, int holeCount) {
  switch(t) {
    case ltreeseg(n, lhs, rhs): return 1 + tssize(lhs, holeCount) + size(rhs);
    case rtreeseg(n, lhs, rhs): return 1 + size(lhs) + tssize(rhs, holeCount); 
    case Hole(n): return holeCount;
  }
}
  
predicate tree(struct Node* node, tree value)
  requires switch(value) { 
    case Nil: return false;
    case tree(node2, lhs, rhs): return node!=0 &*& node==node2 &*& node->count |-> ?c &*& c == size(value) &*&
                                       node->left |-> ?l &*& node->right |-> ?r &*& (l==0 ? lhs==Nil : tree(l, lhs) &*& l->parent |-> node) &*&
                                       (r==0 ? rhs==Nil : tree(r, rhs) &*& r->parent |-> node) &*& malloc_block_Node(node); 
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

fixpoint tree plugHole(treeseg ts, tree plug) {
  switch(ts) {
    case ltreeseg(n, lhs, rhs): return tree(n, plugHole(lhs, plug), rhs);
    case rtreeseg(n, lhs, rhs): return tree(n, lhs, plugHole(rhs, plug));
    case Hole(n): return plug;
  }
}
@*/

struct Node* create(struct Node* parent)
  requires emp;
  ensures result!=0 &*& tree(result, tree(result, Nil, Nil)) &*& result->parent |-> parent;
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
  n->left = 0;
  n->right = 0;
  n->parent = parent;
  n->count = 1;
  //@ close tree(n, tree(n, Nil, Nil)); 
  return n;
}

/*@
predicate isTree(struct Node* n, tree value) 
  requires tree(?root, value) &*& root->parent |-> 0 &*& contains(value, n) == true;

fixpoint bool contains(tree value, struct Node* n) {
  switch(value) {
    case Nil: return false;
    case tree(r, lhs, rhs): return n==r || contains(lhs, n) || contains(rhs, n);
  }
}
@*/

/*@
fixpoint tree valueOf(tree value, struct Node * n) {
  switch(value) {
    case Nil: return Nil;
    case tree(r, lhs, rhs): return n==r ? tree(r, lhs, rhs) : (contains(lhs, n) ? valueOf(lhs, n) : valueOf(rhs, n));
  }
}

fixpoint context upsideDownMinus(tree value, struct Node* n, context con) {
  switch(value) {
    case Nil: return Root;
    case tree(r, lhs, rhs): return r==n ? con : (contains(lhs, n) ? 
        upsideDownMinus(lhs, n, lcontext(r, con, rhs)) : upsideDownMinus(rhs, n, rcontext(r, lhs, con)) );
  }
}

lemma void tree2context(struct Node* root, struct Node* n, tree value) 
  requires tree(root, value) &*& context(root, ?cvalue, size(value)) &*& contains(value, n) == true; 
  ensures context(n, upsideDownMinus(value, n, cvalue), size(valueOf(value, n))) &*& tree(n, valueOf(value, n));
{
  switch(value) {
    case Nil: return;
    case tree(root2, lhs, rhs): 
      if(root == n) {
        open tree(root, value);
        close tree(root, value);
      } else {
        open tree(root, value);
        if(contains(lhs, n)) {
          struct Node* l = root->left;
          struct Node* r = root->right;
          close context(l, lcontext(root, cvalue, rhs), size(lhs));
          tree2context(l, n, lhs);
        } else {
          struct Node* l = root->left;
          struct Node* r = root->right;
          close context(r, rcontext(root, lhs, cvalue), size(rhs));
          tree2context(r, n, rhs);
        }
      }
  }
}
@*/



struct Node* addLeftChild(struct Node* node)
  /*@ requires context(node, ?value, 1) &*& node!=0 &*& node->left |-> 0 &*& node->right |-> 0 &*&
               malloc_block_Node(node) &*& node->count |-> 1; @*/
  /*@ ensures context(node, value, 2) &*& node!=0 &*& node->left |-> result &*& node->right |-> 0 &*&
               malloc_block_Node(node) &*& node->count |-> 2 &*& 
               tree(result, tree(result, Nil, Nil)); @*/
{
    struct Node* child = create(node);
    node->left = child;
    fix(node);
    return child;
}

void fix(struct Node* node)
  /*@ requires node->count |-> ?c &*& context(node, ?value, c) &*& node!=0; @*/   
  /*@ ensures context(node, value, c + 1) &*& node->count |-> c + 1; @*/
{
  int tmp = node->count;
  node->count = tmp + 1;
  //@ open context(node, value, c);
  struct Node* parent = node->parent;
  if(parent==0){
  } else {
    fix(parent);
  }
  //@ close context(node, value, c+1);
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

void main() {
  struct Node* mytree = create(0);
  struct Node* child1 = addLeftChild(mytree);
}
  