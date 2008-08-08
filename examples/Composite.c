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
    //case tree(r, lhs, rhs): return (n==r && ! contains(lhs, n) && ! contains(rhs, n)) || (n!=r && contains(lhs, n) && !contains(rhs, n)) || (n!=r && !contains(lhs, n) && contains(rhs, n));
  }
}

fixpoint bool disjoint(tree lhs, tree rhs) {
  switch (lhs) {
    case Nil: return true;
    case tree(r, left, right): return !contains(rhs, r) && disjoint(left, rhs) && disjoint(right, rhs);
  }
}

fixpoint bool uniqueNodes(tree t) {
  switch (t) {
    case Nil: return true;
    case tree(r, left, right): return !contains(left, r) && !contains(right, r) && disjoint(left, right) && uniqueNodes(left) && uniqueNodes(right);
  }
}

fixpoint bool inContext(context con, struct Node* n){
  switch(con){
    case Root: return false;
    case lcontext(r, lcon, rhs): return r==n || inContext(lcon, n) || contains(rhs, n);
    case rcontext(r, lhs, rcon): return r==n || contains(lhs, n) || inContext(rcon, n);
  }
}

fixpoint bool disjointContext(context con, tree t) {
  switch (t) {
    case Nil: return true;
    case tree(r, left, right): return !inContext(con, r) && disjointContext(con, left) && disjointContext(con, right);
  }
}

fixpoint bool contextUniqueNodes(context con) {
  switch (con) {
    case Root: return true;
    case lcontext(r, lcon, rhs): return !inContext(lcon, r) && !contains(rhs, r) && disjointContext(lcon, rhs) && contextUniqueNodes(lcon) && uniqueNodes(rhs);
    case rcontext(r, lhs, rcon): return !contains(lhs, r) && !inContext(rcon, r) && disjointContext(rcon, lhs) && uniqueNodes(lhs) && contextUniqueNodes(rcon);
  }
}

lemma void treeDistinct(struct Node *root, struct Node *node)
  requires tree(root, ?t) &*& node->left |-> ?l;
  ensures tree(root, t) &*& node->left |-> l &*& !contains(t, node);
{
  open tree(root, t);
  switch (t) {
    case Nil:
    case tree(r, lhs, rhs):
      struct Node *left = root->left;
      struct Node *right = root->right;
      if (left == 0) {
      } else {
        treeDistinct(left, node);
      }
      if (right == 0) {
      } else {
        treeDistinct(right, node);
      }
  }
  close tree(root, t);
}

lemma void treesDisjoint(struct Node *root1, struct Node *root2)
  requires tree(root1, ?t1) &*& tree(root2, ?t2);
  ensures tree(root1, t1) &*& tree(root2, t2) &*& disjoint(t1, t2) == true;
{
  open tree(root1, t1);
  switch (t1) {
    case Nil:
    case tree(r, lhs, rhs):
      treeDistinct(root2, root1);
      struct Node *left = root1->left;
      struct Node *right = root1->right;
      if (left == 0) {
      } else {
        treesDisjoint(left, root2);
      }
      if (right == 0) {
      } else {
        treesDisjoint(right, root2);
      }
  }
  close tree(root1, t1);
}

lemma void disjointNil(tree t)
  requires true;
  ensures disjoint(t, Nil) == true;
{
  switch (t) {
    case Nil: return;
    case tree(r, lhs, rhs):
      disjointNil(lhs);
      disjointNil(rhs);
  }
}

lemma void treeUniqueNodes(struct Node *root)
  requires tree(root, ?t);
  ensures tree(root, t) &*& uniqueNodes(t) == true;
{
  open tree(root, t);
  switch (t) {
    case Nil:
      return;
    case tree(r, lhs, rhs):
      struct Node *left = root->left;
      struct Node *right = root->right;
      if (left == 0) {
      } else {
        treeDistinct(left, root);
        treeUniqueNodes(left);
      }
      if (right == 0) {
        disjointNil(lhs);
      } else {
        treeDistinct(right, root);
        treeUniqueNodes(right);
      }
      if (left != 0 && right != 0) {
        treesDisjoint(left, right);
      } else {
      }
      assert(!contains(lhs, r));
      assert(!contains(rhs, r));
      assert(disjoint(lhs, rhs));
  }
  close tree(root, t);
}

lemma void contextDistinct(struct Node* c, struct Node* n)
  requires context(c, ?con, ?count) &*& n->left |-> ?x;
  ensures context(c, con, count) &*& n->left |-> x &*& !inContext(con, n);
{
  open context(c, con, count);
  switch(con) {
    case Root:
      return ;
    case lcontext(r, lcon, rhs):
      struct Node *left = r->left;
      struct Node *right = r->right;
      contextDistinct(r, n);
      if(right!=0){
        treeDistinct(right, n);
      } else {}
    case rcontext(r, lhs, rcon):
      struct Node *left = r->left;
      struct Node *right = r->right;
      contextDistinct(r, n);
      if(left!=0){
        treeDistinct(left, n);
      } else {}
  }
  close context(c, con, count);
}

lemma void treeContextDisjoint(struct Node* n, struct Node* c)
  requires tree(n, ?t) &*& context(c, ?con, ?cc);
  ensures tree(n, t) &*& context(c, con, cc) &*& disjointContext(con, t) == true;
{
  open tree(n, t);
  switch(t) {
    case Nil: 
      return;
    case tree(r, lhs, rhs):
      struct Node* left = r->left;
      struct Node* right = r->right;
      contextDistinct(c, r);
      if (left == 0) {
      } else {
        treeContextDisjoint(left, c);
      }
      if (right == 0) {
      } else {
        treeContextDisjoint(right, c);
      }
  }
  close tree(n, t);
}

lemma void contextUniqueNodes(struct Node* n)
  requires context(n, ?con, ?count);
  ensures context(n, con, count) &*& contextUniqueNodes(con) == true;
{
  open context(n, con, count);
  switch(con){
    case Root: 
      return;
    case lcontext(r, lcon, rhs):
      struct Node* left = r->left;
      struct Node* right = r->right;
      struct Node* par = n->parent;
      contextDistinct(par, r);
      contextUniqueNodes(r);
      if(right == 0){
      }  else {
        treeDistinct(right, r);
        treeContextDisjoint(right, par);
        treeUniqueNodes(right);
      }
    case rcontext(r, lhs, rcon):
      struct Node* left = r->left;
      struct Node* right = r->right;
      struct Node* par = n->parent;
      contextDistinct(par, r);
      contextUniqueNodes(r);
      if(left == 0){
      }  else {
        treeDistinct(left, r);
        treeContextDisjoint(left, par);
        treeUniqueNodes(left);
      }
  }
  close context(n, con, count);
}
    
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



fixpoint tree reverse(context con, tree val) {
  switch(con){
    case Root: return val; 
    case lcontext(r, lcon, rhs): return reverse(lcon, tree(r, val, rhs)); 
    case rcontext(r, lhs, rcon): return reverse(rcon, tree(r, lhs, val));
  }
}

fixpoint int contextSize(context con) {
  switch(con){
    case Root: return 0; 
    case lcontext(r, lcon, rhs): return 1 + contextSize(lcon);
    case rcontext(r, lhs, rcon): return 1 + contextSize(rcon);
  }
}

lemma void upsideDownMinusSize(tree t, struct Node* n, context con)
  requires true;
  ensures contextSize(con) <= contextSize(upsideDownMinus(t, n, con));
{
  switch(t){
    case Nil:
    case tree(r, lhs, rhs):
      if(r==n){
      } else {
        if(contains(lhs, n)){
          upsideDownMinusSize(lhs, n, lcontext(r, con, rhs));
        } else {
          upsideDownMinusSize(rhs, n, rcontext(r, lhs, con));
        }
      }
  }
}

lemma void upsideDownMinusIsRoot(struct Node* r, tree lhs, tree rhs, struct Node* node, context con)
  requires con==upsideDownMinus(tree(r, lhs, rhs), node, con);
  ensures node == r;
{
  if(r==node){
  } else {
    if(contains(lhs, node)){
       upsideDownMinusSize(lhs, node, lcontext(r, con, rhs));  
    } else {
       upsideDownMinusSize(rhs, node, rcontext(r, lhs, con));  
    }
  }
}



lemma void containsValueOf(tree t, struct Node* n, tree v, struct Node* n2)
  requires uniqueNodes(t)==true &*& valueOf(t, n)==v &*& contains(v, n2)==true;
  ensures contains(t, n2)==true;
{
  switch(t) {
    case Nil: 
    case tree(r, lhs, rhs):
      if(r==n){
      } else {
        if(contains(lhs, n)){
          containsValueOf(lhs, n, v, n2);
        } else {
          containsValueOf(rhs, n, v, n2);
        }
      }
  }  
}

fixpoint context upsideDownMinus(tree value, struct Node* n, context con) {
  switch(value) {
    case Nil: return con;
    case tree(r, lhs, rhs): return r==n ? con : (contains(lhs, n) ? 
        upsideDownMinus(lhs, n, lcontext(r, con, rhs)) : upsideDownMinus(rhs, n, rcontext(r, lhs, con)) );
  }
}

lemma void disjointContains(tree t1, tree t2, struct Node* n)
  requires contains(t2, n)==true &*& disjoint(t1, t2)==true;
  ensures ! contains(t1, n);
{
  switch(t1){
    case Nil:
    case tree(r, lhs, rhs):
      disjointContains(lhs, t2, n);
      disjointContains(rhs, t2, n);
  }
}

lemma void upsideDownMinusParentLeft(struct Node* parent, tree oldval, struct Node* child, tree lhs, tree rhs, tree rhs2, context con)
  requires contains(oldval, parent)==true &*& valueOf(oldval, parent)==tree(parent, tree(child, lhs, rhs), rhs2) &*& 
           parent!=child &*& uniqueNodes(oldval)==true;
  ensures upsideDownMinus(oldval, child, con) == lcontext(parent, upsideDownMinus(oldval, parent, con), rhs2);
{
  switch(oldval) {
    case Nil: 
    case tree(r, mylhs, myrhs):
      if(r==parent){
      } else {
        if(contains(mylhs, parent)){
          upsideDownMinusParentLeft(parent, mylhs, child, lhs, rhs, rhs2, lcontext(r, con, myrhs));        
          containsValueOf(mylhs, parent, tree(parent, tree(child, lhs, rhs), rhs2), child);
       } else {
          upsideDownMinusParentLeft(parent, myrhs, child, lhs, rhs, rhs2, rcontext(r, mylhs, con));
          containsValueOf(myrhs, parent, tree(parent, tree(child, lhs, rhs), rhs2), child);
          disjointContains(mylhs, myrhs, child);
        }
      }
  }
}

lemma void valueOfValueOf(tree t, struct Node *r, tree v, struct Node *n)
  requires uniqueNodes(t) == true &*& contains(t, r) == true &*& valueOf(t, r) == v &*& contains(v, n) == true;
  ensures valueOf(t, n) == valueOf(v, n);
{
  switch (t) {
    case Nil:
    case tree(tr, lhs, rhs):
      if (tr == r) {
      } else {
        if (contains(lhs, r)) {
          containsValueOf(lhs, r, v, n);
          valueOfValueOf(lhs, r, v, n);
        } else {
          containsValueOf(rhs, r, v, n);
          disjointContains(lhs, rhs, n);
          valueOfValueOf(rhs, r, v, n);
        }
      }
  }
}

lemma void uniqueNodesValueOf(tree t, struct Node *n)
  requires uniqueNodes(t) == true &*& contains(t, n) == true;
  ensures uniqueNodes(valueOf(t, n)) == true;
{
  switch (t) {
    case Nil:
    case tree(r, lhs, rhs):
      if (r == n) {
      } else {
        if (contains(lhs, n)) {
          uniqueNodesValueOf(lhs, n);
        } else {
          uniqueNodesValueOf(rhs, n);
        }
      }
  }
}

lemma void valueOfRoot(tree t, struct Node *n, struct Node *r, tree lhs, tree rhs)
  requires valueOf(t, n) == tree(r, lhs, rhs);
  ensures n == r;
{
  switch (t) {
    case Nil:
    case tree(tr, tlhs, trhs):
      if (tr == n) {
      } else {
        if (contains(tlhs, n)) {
          valueOfRoot(tlhs, n, r, lhs, rhs);
        } else {
          valueOfRoot(trhs, n, r, lhs, rhs);
        }
      }
  }
}

lemma void upsideDownMinusLContext(tree t0, struct Node * tr, tree t, struct Node* n, tree nlhs, tree nrhs, context con, struct Node* r, context lcon, tree rhs)
  requires
    uniqueNodes(t0) == true &*&
    contains(t0, tr) == true &*&
    upsideDownMinus(t0, n, Root) == upsideDownMinus(t, n, con) &*&
    upsideDownMinus(t, n, con) == lcontext(r, lcon, rhs) &*&
    contains(t, n)==true &*&
    t == valueOf(t0, tr) &*&
    valueOf(t0, n) == tree(n, nlhs, nrhs) &*&
    tr != n;
  ensures
    contains(t0, r) == true &*&
    valueOf(t0, r) == tree(r, tree(n, nlhs, nrhs), rhs);
{
  switch (t) {
    case Nil:
    case tree(tr0, tlhs, trhs):
      valueOfRoot(t0, tr, tr0, tlhs, trhs);
      assert(tr0 == tr);
      if (contains(tlhs, n)) {
        switch (tlhs) {
          case Nil:
          case tree(rtlhs, tlhslhs, tlhsrhs):
            if (rtlhs == n) {
              assert(upsideDownMinus(t, n, con) == lcontext(tr, con, trhs));
            } else {
              containsValueOf(t0, tr, tree(tr, tlhs, trhs), rtlhs);
              valueOfValueOf(t0, tr, tree(tr, tlhs, trhs), rtlhs);
              uniqueNodesValueOf(t0, tr);
              assert(tr != rtlhs);
              upsideDownMinusLContext(t0, rtlhs, tlhs, n, nlhs, nrhs, lcontext(tr, con, trhs), r, lcon, rhs);

            }
        }
      } else {
        switch (trhs) {
          case Nil:
          case tree(rtrhs, trhslhs, trhsrhs):
            if (rtrhs == n) {
              assert(upsideDownMinus(t, n, con) == rcontext(tr, tlhs, con));
            } else {
              containsValueOf(t0, tr, t, rtrhs);
              valueOfValueOf(t0, tr, t, rtrhs);
              uniqueNodesValueOf(t0, tr);
              assert(tr != rtrhs);
              disjointContains(tlhs, trhs, rtrhs);
              assert(!contains(tlhs, rtrhs));
              upsideDownMinusLContext(t0, rtrhs, trhs, n, nlhs, nrhs, rcontext(tr, tlhs, con), r, lcon, rhs);

            }
        }
      }
  }
}

lemma void valueOfNotNil(tree t, struct Node *n)
  requires contains(t, n) == true;
  ensures valueOf(t, n) != Nil;
{
  switch (t) {
    case Nil:
    case tree(r, lhs, rhs):
      if (r == n) {
      } else {
        if (contains(lhs, n)) {
          valueOfNotNil(lhs, n);
        } else {
          valueOfNotNil(rhs, n);
        }
      }
  }
}


lemma void context2tree(struct Node* theroot, struct Node* node, context contextval, tree oldval)
  requires tree(node, ?v) &*& context(node, contextval, size(v)) &*& getroot(contextval, node) == theroot
           &*& contextval == upsideDownMinus(oldval, node, Root)
           &*& contains(oldval, node) == true &*& uniqueNodes(oldval) == true; 
  ensures tree(theroot, replace(oldval, node, v)) &*& theroot->parent |-> 0;
{
  switch(contextval) {
    case Root: 
      switch(oldval){
        case Nil: return;
        case tree(r, lhs, rhs): 
          upsideDownMinusIsRoot(r, lhs, rhs, node, Root);
          assert(r==node);
          return;
      }
      assert(node==theroot);
      open context(node, contextval, size(v));
    case lcontext(r, lcon, rhs):
      open context(node, contextval, size(v));
      struct Node* nodeParent = node->parent; 
      valueOfNotNil(oldval, node);
      switch(valueOf(oldval, node)){
        case Nil: return; 
        case tree(node0, nodeLhs, nodeRhs):
          valueOfRoot(oldval, node, node0, nodeLhs, nodeRhs);
          assert(node == node0);
          close tree(nodeParent, tree(nodeParent, v, rhs));
         // assert(valueOf(oldval, nodeParent)==tree(nodeParent, tree(node, nodeLhs, nodeRhs), rhs));
          switch(oldval){
            case Nil: return;
            case tree(oldvalroot, oldvallhs, oldvalrhs):
              assert(valueOf(oldval, oldvalroot)==oldval);
              assert(nodeParent == r);
              upsideDownMinusLContext(oldval, oldvalroot, oldval, node, nodeLhs, nodeRhs, Root, nodeParent, lcon, rhs);
              assert(valueOf(oldval, node) == tree(node, nodeLhs, nodeRhs));
              assert(valueOf(oldval, nodeParent) == tree(nodeParent, tree(node, nodeLhs, nodeRhs), rhs));
              upsideDownMinusParentLeft(nodeParent, oldval, node, nodeLhs, nodeRhs, rhs, Root);
              context2tree(theroot, nodeParent, lcon, oldval);
          }
      }
    case rcontext(r, lhs, rcon):
      open context(node, contextval, size(v));
      struct Node* nodeParent = node->parent;
      close tree(nodeParent, tree(nodeParent, lhs, v));
      context2tree(theroot, nodeParent, rcon, oldval);
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
  //@ uniqueNodes(root);
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



lemma void containsReverse1(context con, tree t, struct Node* n)
  requires contains(t, n)==true &*& !inContext(con, n);
  ensures contains(reverse(con, t), n)==true;
{
  switch(con){
    case Root: 
    case lcontext(r, lcon, rhs): 
      containsReverse1(lcon, t, n);
    case rcontext(r, lhs, rcon):
      containsReverse1(rcon, t, n);
  }
}

lemma void containsReverse(context con, tree t, struct Node* n)
  requires true;
  ensures contains(reverse(con, t), n) == ( (contains(t, n) && !inContext(con, n)) || (!contains(t, n) && inContext(con, n)) );
{
  switch(con){
    case Root: 
      if(contains(t, n)){
      } else {}
    case lcontext(r, lcon, rhs):
      containsReverse(lcon, tree(r, t, rhs), n);
      if(contains(reverse(con, t), n)){
        if(contains(t, n)){
        } else {
          if(r==n) {
            assert(contains(reverse(lcon, tree(r, t, rhs)), n) == ((contains(tree(r, t, rhs), n) && !inContext(lcon, n)) 
                                                                || (!contains(tree(r, t, rhs), n) && inContext(lcon, n))) );
            //assert(!inContext(lcon, n));
            //assert(!contains(rhs, n));
          } else {}
          
          //assert(inContext(con, n));
        }
      } else {

      }
    case rcontext(r, lhs, rcon):
      containsReverse(rcon, tree(r, lhs, t), n);
      if(contains(reverse(con, t), n)){
        if(contains(t, n)){
        } else {}
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

lemma void reverseLemma(tree t, struct Node* node, context con, tree newValue)
  requires contains(t, node) == true &*& inContext(con, node) == false;
  ensures reverse(upsideDownMinus(t, node, con), newValue) == replace(reverse(con, t), node, newValue);
{
  switch(t){
    case Nil: 
      
    case tree(r, lhs, rhs): 
      if(r == node){
        replaceReverseComm(con, t, node, newValue);
      } else {
        if(contains(lhs, node)){
          reverseLemma(lhs, node, lcontext(r, con, rhs), newValue);





          assert(reverse(upsideDownMinus(lhs, node, lcontext(r, con, rhs)), newValue) == replace(reverse(lcontext(r, con, rhs), lhs), node, newValue));
          
          assert(upsideDownMinus(lhs, node, lcontext(r, con, rhs)) == upsideDownMinus(t, node, lcontext(r, con, rhs)) );
          

          assert(reverse(upsideDownMinus(t, node, con), newValue) == replace(reverse(con, t), node, newValue));
        } else {
          reverseLemma(rhs, node, con, newValue);
        }
      }
  }
}


@*/