/*@

inductive tree = empty(Tree node) | nonempty(Tree node, tree left, tree right);

fixpoint int node_count(tree tree) {
    switch (tree) {
        case empty(node): return 1;
        case nonempty(node, left, right): return 1 + node_count(left) + node_count(right);
    }
}

lemma_auto void node_count_positive(tree tree)
    requires true;
    ensures node_count(tree) >= 1;
{
    switch (tree) {
        case empty(node):
        case nonempty(node, left, right):
            node_count_positive(left);
            node_count_positive(right);
    }
}

predicate tree(Tree node, boolean marked; Tree parent, tree shape) =
    node.left |-> ?left &*&
    node.right |-> ?right &*&
    node.mark |-> ?mark &*& (marked ? mark == true : true) &*&
    node.parent |-> parent &*&
    left == null ?
        right == null &*&
        shape == empty(node)
    :
        right != null &*&
        tree(left, marked, node, ?leftShape) &*&
        tree(right, marked, node, ?rightShape) &*&
        shape == nonempty(node, leftShape, rightShape);

predicate stack(Tree parent, Tree current, tree cShape, Tree root, tree rootShape, int stepsLeft) =
    current != null &*&
    parent == null ?
        root == current &*& rootShape == cShape &*& stepsLeft == 0
    :
        parent.left |-> ?left &*&
        parent.right |-> ?right &*&
        parent.mark |-> true &*&
        parent.parent |-> current &*&
        exists<boolean>(?currentIsLeftChild) &*&
        currentIsLeftChild ?
            tree(left, false, parent, ?rightShape) &*& left != null &*&
            stack(right, parent, nonempty(parent, cShape, rightShape), root, rootShape, ?stepsLeft1) &*& stepsLeft1 >= 0 &*&
            stepsLeft == node_count(rightShape) * 2 + 1 + stepsLeft1
        :
            tree(right, true, parent, ?leftShape) &*& right != null &*&
            stack(left, parent, nonempty(parent, leftShape, cShape), root, rootShape, ?stepsLeft1) &*& stepsLeft1 >= 0 &*&
            stepsLeft == 1 + stepsLeft1;

lemma void tree_nonnull(Tree t)
    requires tree(t, ?marked, ?parent, ?shape);
    ensures tree(t, marked, parent, shape) &*& t != null;
{
    open tree(t, marked, parent, shape);
    close tree(t, marked, parent, shape);
}

predicate inv(boolean xIsNew, Tree x, Tree root, tree rootShape, int stepsLeft) =
        xIsNew ?
            tree(x, false, ?parent, ?xShape) &*& stack(parent, x, xShape, root, rootShape, ?stepsLeft1) &*&
            stepsLeft1 >= 0 &*& stepsLeft == node_count(xShape) * 2 - 1 + stepsLeft1
        :
            stack(x, ?child, ?childShape, root, rootShape, stepsLeft) &*& stepsLeft >= 0 &*&
            tree(child, true, x, childShape);
    

@*/

class Tree {
	Tree left, right, parent;
	boolean mark;
	
	static void markTree(Tree root)
	    //@ requires tree(root, false, null, ?rootShape);
	    //@ ensures tree(root, true, null, rootShape);
	{
		Tree x, y;
		x = root;
		//@ tree_nonnull(x);
		//@ close stack(null, root, rootShape, root, rootShape, 0);
		//@ close inv(true, x, root, rootShape, _);
		do
		    //@ invariant inv(?xIsNew, x, root, rootShape, ?stepsLeft) &*& x != null;
		    //@ decreases stepsLeft;
		{
			//@ open inv(_, _, _, _, _);
			//@ if (!xIsNew) open stack(x, _, _, _, _, _);
	  		x.mark = true;
	  		if (x.left == null && x.right == null) {
	    		  	y = x.parent;
	    		  	//@ close inv(false, y, root, rootShape, _);
	  		} else {
	    			y = x.left;
	    			x.left = x.right;
	    			x.right = x.parent;
	    			x.parent = y;
	    			/*@
	    			if (xIsNew) {
	    			    assert tree(y, false, x, ?leftShape);
	    			    close exists(true);
	    			    close stack(x, y, leftShape, root, rootShape, _);
	    			    close inv(true, y, root, rootShape, _);
	    			} else {
	    			    open exists(?markedLeftSubtree);
	    			    if (markedLeftSubtree) {
	    			        close exists(false);
	    			        assert tree(y, false, x, ?rightShape);
	    			        tree_nonnull(x.right);
	    			        close stack(x, y, rightShape, root, rootShape, _);
	    			        close inv(true, y, root, rootShape, _);
	    			    } else {
	    			        close inv(false, y, root, rootShape, _);
	    			    }
	    			}
	    			@*/
	  		}
		 	x = y;
		} while (x != null);
		//@ open inv(_, _, _, _, _);
		//@ open stack(null, _, _, _, _, _);
	}
}

