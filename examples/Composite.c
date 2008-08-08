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
    case lcontext(n, cont, t): return n!=0 &*& n->left |-> node &*& node != 0 &*& n->right |-> ?r &*& n->count |-> ?c &*&
                                      (r==0 ? t==Nil : tree(r, t) &*& r->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n &*&
                                      malloc_block_Node(n);
    case rcontext(n, t, cont): return n!=0 &*& n->right |-> node &*& node!=0 &*& n->left |-> ?l &*& n->count |-> ?c &*&
                                      (l==0 ? t==Nil : tree(l, t) &*& l->parent |-> n) &*& context(n, cont, c) &*& c== holeCount + 1 + size(t) &*& node->parent |-> n &*&
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
  requires tree(?root, value) &*& root!=0 &*& root->parent |-> 0 &*& contains(value, n) == true;

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



fixpoint struct Node* getroot(context val, struct Node* prev) {
  switch(val){
    case Root: return prev;
    case lcontext(r, lcon, rhs): return getroot(lcon, r);
    case rcontext(r, lhs, rcon): return getroot(rcon, r);
  }
}

lemma void tree2context(struct Node* root, struct Node* n, tree value, struct Node* oroot) 
  requires tree(root, value) &*& context(root, ?cvalue, size(value)) &*& contains(value, n) == true &*& getroot(cvalue, root)==oroot; 
  ensures context(n, upsideDownMinus(value, n, cvalue), size(valueOf(value, n))) &*& tree(n, valueOf(value, n)) &*&
          getroot(upsideDownMinus(value, n, cvalue), n) == oroot;
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
          tree2context(l, n, lhs, oroot);
        } else {
          struct Node* l = root->left;
          struct Node* r = root->right;
          close context(r, rcontext(root, lhs, cvalue), size(rhs));
          tree2context(r, n, rhs, oroot);
        }
      }
  }
}


lemma void context2tree(struct Node* theroot, struct Node* node, context contextval)
  requires tree(node, ?v) &*& context(node, contextval, size(v)) &*& getroot(contextval, node) == theroot; 
  ensures tree(theroot, reverse(contextval, v)) &*& theroot->parent |-> 0;
{
  switch(contextval) {
    case Root: open context(node, contextval, size(v));
    case lcontext(r, lcon, rhs): 
      open context(node, contextval, size(v));
      struct Node* nodeParent = node->parent; 
      close tree(nodeParent, tree(nodeParent, v, rhs));
      context2tree(theroot, nodeParent, lcon);
    case rcontext(r, lhs, rcon):
      open context(node, contextval, size(v));
      struct Node* nodeParent = node->parent;
      close tree(nodeParent, tree(nodeParent, lhs, v));
      context2tree(theroot, nodeParent, rcon);
  }
}

fixpoint tree addLeft(tree value, struct Node* node, tree ptr) {
  switch(value){
    case Nil: return Nil;
    case tree(r, lhs, rhs): return r == node ? tree(r, ptr, rhs) : 
                                               (contains(lhs, node) ? tree(r, addLeft(lhs, node, ptr), rhs) : 
                                                                      tree(r, lhs, addLeft(rhs, node, ptr)));
  }
}

fixpoint tree left(tree value) {
  switch(value){
    case Nil: return Nil;
    case tree(r, lhs, rhs): return lhs;
  }
}
@*/

struct Node* addLeftWrapper(struct Node* node)
  //@ requires isTree(node, ?v) &*& valueOf(v, node) == tree(node, Nil, Nil);
  /*@ ensures isTree(node, replace(v, node, tree(node, tree(result, Nil, Nil), Nil))); @*/
{
  //@ open isTree(node, v);
  //@ open tree(?root, v);
  //@ close tree(root, v);
  //@ close context(root, Root, size(v));
  //@ tree2context(root, node, v, root);
  
  //@ open tree(node, ?nodeval);
  //@ struct Node* myr = node->right;
  /*@ if(myr != 0){
        open tree(myr, ?rval);
        close tree(myr, rval);
      } else {} @*/
  //@ struct Node* myl = node->left;
  /*@ if(myl != 0){
        open tree(myl, ?rval);
        close tree(myl, rval);
      } else {} @*/
  struct Node* newChild = addLeftChild(node);
  //@ open tree(newChild, ?childVal);
  //@ close tree(newChild, childVal);
  //@ close tree(node, tree(node, tree(newChild, Nil, Nil), Nil));
  //@ context2tree(root, node, upsideDownMinus(v, node, Root));
  //@ reverseLemma(v, node, Root, tree(node, tree(newChild, Nil, Nil), Nil));
  //@ containsReplace(v, node, tree(node, tree(newChild, Nil, Nil), Nil));
  //@ close isTree(node, replace(v, node, tree(node, tree(newChild, Nil, Nil), Nil)));
  return newChild;
}

/*@
lemma void containsReplace(tree t, struct Node* node, tree plug)
  requires contains(t, node)==true &*& contains(plug, node) == true;
  ensures contains(replace(t, node, plug), node)==true;
{
  switch(t) {
    case Nil: return;
    case tree(r, lhs, rhs):
      if(r==node){     
      } else {
        if(contains(lhs, node)){
          containsReplace(lhs, node, plug);
        } else {
          containsReplace(rhs, node, plug);
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
               tree(result, tree(result, Nil, Nil)) &*& result->parent |-> node; @*/
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

struct Node* doCreate() 
  requires emp;
  ensures isTree(result, tree(result, Nil, Nil));
{
  struct Node* n = malloc(sizeof(Node));
  if(n==0){
    abort();
  } else {
  }
  n->parent = 0;
  n->left = 0;
  n->right = 0;
  n->count = 1;
  
  //@ close tree(n, tree(n, Nil, Nil));
  //@ close isTree(n, tree(n, Nil, Nil));
  return n;
}

void main() {
  struct Node* mytree = doCreate();
  struct Node* child = addLeftWrapper(mytree);
  //@ rotate(child);
  struct Node* child2 = addLeftWrapper(child);
}

/*@
lemma void rotate(struct Node* n)
  requires isTree(?r, ?value) &*& contains(value, n) == true;
  ensures isTree(n, value);
{
  open isTree(r, value);
  close isTree(n, value);
}

fixpoint tree replace(tree ts, struct Node* n, tree plug) {
  switch(ts) {
    case Nil: return Nil;
    case tree(r, lhs, rhs): return r==n ? plug : (contains(lhs, n) ? tree(r, replace(lhs, n, plug), rhs) : tree(r, lhs, replace(rhs, n, plug)) );
  }
}

fixpoint context upsideDownMinus(tree value, struct Node* n, context con) {
  switch(value) {
    case Nil: return con;
    case tree(r, lhs, rhs): return r==n ? con : (contains(lhs, n) ? 
        upsideDownMinus(lhs, n, lcontext(r, con, rhs)) : upsideDownMinus(rhs, n, rcontext(r, lhs, con)) );
  }
}

fixpoint tree reverse(context con, tree val) {
  switch(con){
    case Root: return val; 
    case lcontext(r, lcon, rhs): return reverse(lcon, tree(r, val, rhs)); 
    case rcontext(r, lhs, rcon): return reverse(rcon, tree(r, lhs, val));
  }
}

fixpoint bool inContext(context con, struct Node* n){
  switch(con){
    case Root: return false;
    case lcontext(r, lcon, rhs): return r==n || inContext(lcon, n) || contains(rhs, n);
    case rcontext(r, lhs, rcon): return r==n || contains(lhs, n) || inContext(rcon, n);
  }
}

lemma void containsReverse(context con, tree t, struct Node* n)
  requires true;
  ensures contains(reverse(con, t), n) == (contains(t, n) || inContext(con, n));
{
  switch(con){
    case Root: 
      if(contains(t, n)){
      } else {}
    case lcontext(r, lcon, rhs):
      containsReverse(lcon, tree(r, t, rhs), n);
      if(contains(reverse(con, t), n)){
      } else {
      }
    case rcontext(r, lhs, rcon):
      containsReverse(rcon, tree(r, lhs, t), n);
      if(contains(reverse(con, t), n)){
      } else {
      }
  }
}


lemma void replaceReverseComm(context con, tree t, struct Node* node, tree newValue)
  requires inContext(con, node) == false &*& contains(t, node)==true;
  ensures reverse(con, replace(t, node, newValue)) == replace(reverse(con, t), node, newValue);
{
  switch(con) {
    case Root:
    case lcontext(r, lcon, rhs):
      replaceReverseComm(lcon, tree(r, t, rhs), node, newValue);
      if(contains(reverse(con, t), node)){
        
      } else {
      }
      if(contains(t, node)){
      } else {
      }
      containsReverse(con, t, node);
    case rcontext(r, lhs, rcon):
      replaceReverseComm(rcon, tree(r, lhs, t), node, newValue);
      if(contains(reverse(con, t), node)){
        
      } else {
      }
      if(contains(t, node)){
      } else {
      }
      containsReverse(con, t, node);
  }
}

lemma void revisreplace(tree lhs, tree rhs, struct Node* node, context con, tree newValue)
  requires contains(tree(node, lhs, rhs), node) == true &*& inContext(con, node) == false;
  ensures reverse(con, newValue) == replace(reverse(con, tree(node, lhs, rhs)), node, newValue);
{
  switch(con){
    case Root:
    case lcontext(r, lcon, rhs2): 
      revisreplace(lhs, rhs, node, lcon, tree(r, newValue, rhs2));
      
  }
}


lemma void reverseLemma(tree t, struct Node* node, context con, tree newValue)
  requires contains(t, node) == true &*& inContext(con, node) == false;
  ensures reverse(upsideDownMinus(t, node, con), newValue) == replace(reverse(con, t), node, newValue);
{
  switch(t){
    case Nil: 
      
    case tree(r, lhs, rhs): 
      if(r == node){
        
      } else {
        if(contains(lhs, node)){
          reverseLemma(lhs, node, con, newValue);
        } else {
          reverseLemma(rhs, node, con, newValue);
        }
      }
  }
}


@*/