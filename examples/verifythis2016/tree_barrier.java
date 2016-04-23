/*@

typedef lemma void get_op(predicate(boolean) inv, predicate() pre, predicate(boolean) post)();
    requires inv(?value) &*& pre();
    ensures inv(value) &*& post(value);

typedef lemma void set_op(predicate(boolean) inv, boolean value, predicate() pre, predicate() post)();
    requires inv(?value0) &*& pre();
    ensures inv(value) &*& post();

@*/

class AtomicBoolean {
    //@ predicate valid(predicate(boolean) inv);
    AtomicBoolean()
        //@ requires exists<predicate(boolean)>(?inv) &*& inv(false);
        //@ ensures valid(inv);
    {
        throw new RuntimeException();
    }
    boolean get()
        //@ requires [_]valid(?inv) &*& is_get_op(?op, inv, ?pre, ?post) &*& pre();
        //@ ensures post(result);
    {
        throw new RuntimeException();
    }
    void set(boolean value)
        //@ requires [_]valid(?inv) &*& is_set_op(?op, inv, value, ?pre, ?post) &*& pre();
        //@ ensures post();
    {
        throw new RuntimeException();
    }
}

/*@

inductive tree = empty | tree(Node node, tree left, tree right);

predicate tree(Node node, Node parent; tree tree) =
    node == null ?
        tree == empty
    :
        tree1(node, parent, tree);

predicate tree1(Node node; Node parent, tree tree) =
    [_]node.sense |-> ?sense &*& [_]sense.valid(Node_inv(node)) &*&
    [_]node.left |-> ?left &*&
    [_]node.parent |-> parent &*&
    [_]node.leftTree |-> ?leftTree &*& [_]tree(left, node, leftTree) &*&
    [_]node.right |-> ?right &*&
    [_]node.rightTree |-> ?rightTree &*& [_]tree(right, node, rightTree) &*&
    tree == tree(node, leftTree, rightTree);

predicate senseValuesTrue(tree tree;) =
    switch (tree) {
        case empty: return true;
        case tree(node, left, right): return [1/2]node.senseValue |-> true &*& [1/2]senseValuesTrue0(tree);
    };
    
predicate senseValuesTrue0(tree tree;) =
    switch (tree) {
        case empty: return true;
        case tree(node, left, right): return senseValuesTrue(left) &*& senseValuesTrue(right);
    };
    
predicate_ctor Node_inv(Node node)(boolean value) =
    [_]tree1(node, ?parent, ?tree) &*&
    [1/2]node.senseValue |-> value &*&
    value ?
        [1/2]senseValuesTrue0(tree) &*&
        [1/2]node.grabbed |-> ?grabbed &*&
        [1/2]node.takenBack |-> false &*&
        grabbed ?
            parent != null
        :
            (parent == null ? true : senseValuesTrue(tree))
    :
        [1/2]node.grabbed |-> false &*&
        [1/2]node.takenBack |-> ?takenBack &*&
        takenBack ?
            true
        :
            [1/2]node.senseValue |-> false &*& senseValuesTrue0(tree);

predicate child(Node parent, Node child;) =
    parent != null &*&
    child == null ?
        true
    :
        [_]tree1(child, parent, _) &*&
        [1/2]child.grabbed |-> false;

predicate child_grabbed(Node parent, Node child;) =
    parent != null &*&
    child == null ?
        true
    :
        [1/2]child.grabbed |-> true &*&
        [_]tree1(child, parent, ?childTree) &*&
        senseValuesTrue(childTree);

predicate child_grabbed0(Node parent, Node child;) =
    parent != null &*&
    child == null ?
        true
    :
        [1/2]child.grabbed |-> true;

@*/

class Node {
	final Node left, right;
	//@ tree leftTree;
	//@ tree rightTree;
	//@ boolean senseValue;
	//@ boolean grabbed;
	//@ boolean takenBack;
	
	final Node parent;

	AtomicBoolean sense;
	
	/*@
	
	predicate valid() =
	    [_]tree1(this, ?parent, ?thisTree) &*&
	    [1/2]this.senseValue |-> false &*&
	    [1/2]this.takenBack |-> true &*&
	    (parent == null ? [1/2]this.grabbed |-> false : true) &*&
	    [_]this.left |-> ?left &*& child(this, left) &*&
	    [_]this.right |-> ?right &*& child(this, right);
	
	@*/
	
	static void grab(Node child)
	    //@ requires child(?parent, child);
	    //@ ensures child_grabbed(parent, child);
	{
		if(child != null)
	  	    for (;;)
	  	        //@ invariant child(parent, child);
	  	    {
	  	        /*@
	  	        predicate pre() = child(parent, child);
	  	        predicate post(boolean value) = value ? child_grabbed(parent, child) : child(parent, child); 
	  	        lemma void get_op()
	  	            requires Node_inv(child)(?value) &*& pre();
	  	            ensures Node_inv(child)(value) &*& post(value);
	  	        {
	  	            open pre();
	  	            open Node_inv(child)(value);
	  	            if (value) child.grabbed = true;
	  	            close Node_inv(child)(value);
	  	            close post(value);
	  	        }
	  	        @*/
	  	        //@ open [_]tree1(child, _, _);
	  	        //@ produce_lemma_function_pointer_chunk(get_op) : get_op(Node_inv(child), pre, post)() { call(); };
	  	        //@ close pre();
	  	        boolean result = child.sense.get();
	  	        //@ open post(result);
	  	        if (result) break;
	  	    }
		
		//@ if (child == null) { open child(parent, child); }
	}
	
	void ungrab(Node child)
	    //@ requires child_grabbed(?parent, child);
	    //@ ensures child(parent, child);
	{
	    if (child != null) {
	        
	            /*@
	            predicate pre() = [_]child.parent |-> parent &*& child_grabbed(parent, child) &*& child != null;
	            predicate post() = child(parent, child);
	            lemma void set_op()
	                requires Node_inv(child)(?value) &*& pre();
	                ensures Node_inv(child)(false) &*& post();
	            {
	                open Node_inv(child)(value);
	                open pre();
	                child.grabbed = false;
	                open tree1(child, _, _);
	                open senseValuesTrue(_);
	                child.senseValue = false;
	                close post();
	                close Node_inv(child)(false);
	            }
	            @*/
	            //@ produce_lemma_function_pointer_chunk(set_op) : set_op(Node_inv(child), false, pre, post)() { call(); };
	            //@ close pre();
	            child.sense.set(false);
	            //@ open post();
	        
	    }
	    //@ if (child == null) { open child_grabbed(parent, child); }
	}

	void barrier()
		//@ requires valid();
		//@ ensures  valid();
	{
		// synchronization phase
		grab(left);
		grab(right);
		
		{
		    /*@
		    predicate pre() =
		        [1/2]this.senseValue |-> false &*&
		        [1/2]this.takenBack |-> true &*&
		        [_]tree1(this, _, _) &*&
		        [_]this.left |-> ?left &*& child_grabbed(this, left) &*&
		        [_]this.right |-> ?right &*& child_grabbed(this, right);
		    predicate post() =
		        [1/2]takenBack |-> false &*&
		        [_]this.left |-> ?left &*& child_grabbed0(this, left) &*&
		        [_]this.right |-> ?right &*& child_grabbed0(this, right) &*&
		        [_]tree1(this, ?parent, ?thisTree) &*& parent == null ? senseValuesTrue(thisTree) : true;
		    lemma void set_op()
		        requires Node_inv(this)(?value0) &*& pre();
		        ensures Node_inv(this)(true) &*& post();
		    {
		        open Node_inv(this)(_);
		        open pre();
		        open child_grabbed(this, left);
		        open child_grabbed(this, right);
		        assert [_]tree1(this, _, ?thisTree);
		        open tree1(this, _, thisTree);
		        open tree(this.left, _, _);
		        open tree(this.right, _, _);
		        this.senseValue = true;
		        close senseValuesTrue0(thisTree);
		        close senseValuesTrue(thisTree);
		        
		        assert senseValuesTrue(thisTree); /// <<--- property requested established here.
		        takenBack = false;
		        close Node_inv(this)(true);
		        close post();
		    }
		    @*/
		    //@ produce_lemma_function_pointer_chunk(set_op) : set_op(Node_inv(this), true, pre, post)() { call(); };
		    //@ close pre();
		    sense.set(true);
		    //@ open post();
		}
		
		//@ assert [_]parent |-> ?p &*& p == null ? [_]tree1(this, null, ?thisTree) &*& senseValuesTrue(thisTree) : true;

		// wake-up phase
		if(parent == null) {
		    /*@
		    predicate pre() =
		        [1/2]takenBack |-> false &*&
		        [_]this.left |-> ?left &*& child_grabbed0(this, left) &*&
		        [_]this.right |-> ?right &*& child_grabbed0(this, right) &*&
		        [_]tree1(this, null, ?thisTree) &*& senseValuesTrue(thisTree);
		    predicate post() =
		        [1/2]takenBack |-> true &*&
		        [1/2]senseValue |-> false &*&
		        [_]this.left |-> ?left &*& child_grabbed(this, left) &*&
		        [_]this.right |-> ?right &*& child_grabbed(this, right);
		    lemma void set_op()
		        requires Node_inv(this)(?value0) &*& pre();
		        ensures Node_inv(this)(false) &*& post();
		    {
		        open Node_inv(this)(value0);
		        open pre();
		        open tree1(this, null, ?thisTree);
		        open senseValuesTrue(thisTree);
		        senseValue = false;
		        open senseValuesTrue0(thisTree);
		        close child_grabbed(this, left);
		        close child_grabbed(this, right);
		        takenBack = true;
		        close post();
		        close Node_inv(this)(false);
		    }
		    @*/
		    //@ produce_lemma_function_pointer_chunk(set_op) : set_op(Node_inv(this), false, pre, post)() { call(); };
		    //@ close pre();
	  	    sense.set(false);
	  	    //@ open post();
	  	} else {
	  	
	  	//@ assert [_]tree1(this, ?parent, ?thisTree);

		for (;;)
		    //@ requires [_]tree1(this, parent, thisTree) &*& [1/2]takenBack |-> false;
		    //@ ensures [1/2]takenBack |-> true &*& [1/2]this.senseValue |-> false &*& senseValuesTrue0(thisTree);
		{
		    {
		    /*@
		    predicate pre() = [_]tree1(this, parent, thisTree) &*& [1/2]takenBack |-> false;
		    predicate post(boolean value) =
		        [1/2]takenBack |-> !value &*&
		        value ? true :
		            [1/2]this.senseValue |-> false &*& senseValuesTrue0(thisTree);
		    lemma void get_op()
		        requires Node_inv(this)(?value) &*& pre();
		        ensures Node_inv(this)(value) &*& post(value);
		    {
		        open Node_inv(this)(value);
		        open pre();
		        if (value) {
		        } else {
		            takenBack = true;
		        }
		        close post(value);
		        close Node_inv(this)(value);
		    }
		    @*/
		    //@ produce_lemma_function_pointer_chunk(get_op) : get_op(Node_inv(this), pre, post)() { call(); };
		    //@ close pre();
		    boolean result = sense.get();
		    //@ open post(result);
		    if (!result)
		        break;
		    }
		}
		
		//@ open [_]tree1(this, parent, thisTree);
		//@ open senseValuesTrue0(thisTree);
		//@ close child_grabbed(this, left);
		//@ close child_grabbed(this, right);
		
		}
		
		ungrab(left);
		ungrab(right);
	}
}
