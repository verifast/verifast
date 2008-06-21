/* typedef enum ColorType { Red = 0, Black = 1 } ColorType; */

struct RedBlackNode
{
    int  Element;
    struct RedBlackNode * Left;
    struct RedBlackNode * Right;
    int    Color;
};

/*@
predicate subtree(struct RedBlackNode * root, struct RedBlackNode * NullNode)
  requires root->Element |-> _ &*& root->Left |-> ?l &*& root->Right |-> ?r &*& root->Color |-> _ &*& malloc_block_RedBlackNode(root)
    &*& (l == NullNode ? emp : subtree(l, NullNode)) &*& (r == NullNode ? emp : subtree(r, NullNode));

predicate tree(struct RedBlackNode * root, struct RedBlackNode * NullNode)
  requires root->Element |-> _ &*& root->Left |-> NullNode &*& root->Right |-> ?r &*& root->Color |-> _ &*& malloc_block_RedBlackNode(root)
    &*& (r == NullNode ? emp : subtree(r, NullNode));
@*/

struct RedBlackNode *
MakeNullNode()
  //@ requires emp;
  //@ ensures subtree(result, result);
{
    struct RedBlackNode *NullNode = malloc( sizeof( struct RedBlackNode ) );
    NullNode->Left = NullNode;
    NullNode->Right = NullNode;
    NullNode->Color = (1 /* Black */);
    NullNode->Element = 12345;
    //@ close subtree(NullNode, NullNode);
    return NullNode;
}

struct RedBlackNode *
MakeRootNode(struct RedBlackNode * NullNode)
  //@ requires subtree(NullNode, NullNode);
  //@ ensures tree(result, NullNode) &*& subtree(NullNode, NullNode);
{
    /* Create the header node */
    struct RedBlackNode * T = malloc( sizeof( struct RedBlackNode ) );
    /* To prove disjointness */
    //@ open subtree(NullNode, NullNode);
    //@ close subtree(NullNode, NullNode);
    T->Element = (0 - 10000);
    T->Left = NullNode;
    T->Right = NullNode;
    T->Color = (1 /* Black */);
    //@ close tree(T, NullNode);
    return T;
}

/* Print the subtree, watch out for NullNode, */
/* and skip header */

void
DoPrint( struct RedBlackNode * T, struct RedBlackNode * NullNode )
  //@ requires T == NullNode ? emp : subtree(T, NullNode);
  //@ ensures T == NullNode ? emp : subtree(T, NullNode);
{
    if( T != NullNode )
    {
        //@ open subtree(T, NullNode);
        struct RedBlackNode * left = T->Left;
        DoPrint( left, NullNode );
        // Output( T->Element );
        struct RedBlackNode * right = T->Right;
        DoPrint( right, NullNode );
        //@ close subtree(T, NullNode);
    }
    else
    {
    }
}

void
PrintTree( struct RedBlackNode * T, struct RedBlackNode * NullNode )
  //@ requires tree(T, NullNode);
  //@ ensures tree(T, NullNode);
{
    //@ open tree(T, NullNode);
    struct RedBlackNode * right = T->Right;
    DoPrint( right, NullNode );
    //@ close tree(T, NullNode);
}

struct RedBlackNode *
MakeEmptyRec( struct RedBlackNode * T, struct RedBlackNode * NullNode )
  //@ requires T == NullNode ? emp : subtree(T, NullNode);
  //@ ensures emp &*& result == NullNode;
{
    if( T != NullNode )
    {
        //@ open subtree(T, NullNode);
        struct RedBlackNode * left = T->Left;
        MakeEmptyRec( left, NullNode );
        struct RedBlackNode * right = T->Right;
        MakeEmptyRec( right, NullNode );
        free( T );
    }
    else
    {
    }
    return NullNode;
}

struct RedBlackNode *
MakeEmpty( struct RedBlackNode * T, struct RedBlackNode * NullNode )
  //@ requires tree(T, NullNode);
  //@ ensures tree(T, NullNode) &*& result == T;
{
    //@ open tree(T, NullNode);
    struct RedBlackNode * right = T->Right;
    right = MakeEmptyRec( right, NullNode );
    T->Right = right;
    //@ close tree(T, NullNode);
    return T;
}

/*@
predicate tseg(struct RedBlackNode * root, struct RedBlackNode * NullNode, struct RedBlackNode * hole, int holeValue)
  requires
    root->Element |-> ?e &*& root->Left |-> ?l &*& root->Right |-> ?r &*& root->Color |-> _ &*& malloc_block_RedBlackNode(root)
    &*& holeValue < e
        ? (l == hole ? emp : tseg(l, NullNode, hole, holeValue))
          &*& (r == NullNode ? emp : subtree(r, NullNode))
        : (l == NullNode ? emp : subtree(l, NullNode))
          &*& (r == hole ? emp : tseg(r, NullNode, hole, holeValue));

lemma void tseg_tree_distinct_lemma(struct RedBlackNode * root, struct RedBlackNode * hole, int holeValue, struct RedBlackNode * NullNode)
  requires tseg(root, NullNode, hole, holeValue) &*& subtree(hole, NullNode);
  ensures tseg(root, NullNode, hole, holeValue) &*& subtree(hole, NullNode) &*& root != hole;
{
  open tseg(root, NullNode, hole, holeValue);
  open subtree(hole, NullNode);
  close subtree(hole, NullNode);
  close tseg(root, NullNode, hole, holeValue);
}   

@*/

// Returns the node containing value X, or NullNode if X is not in the subtree.

struct RedBlackNode *
Find( int X, struct RedBlackNode * T, struct RedBlackNode * NullNode )
  //@ requires T == NullNode ? emp : subtree(T, NullNode);
  //@ ensures T == NullNode ? result == NullNode : result == NullNode ? subtree(T, NullNode) : result == T ? subtree(result, NullNode) : tseg(T, NullNode, result, X) &*& subtree(result, NullNode);
{
    if( T == NullNode ) {
        return NullNode;
    } else {
        //@ open subtree(T, NullNode);
        int element = T->Element;
        if( X < element ) {
            struct RedBlackNode * left = T->Left;
            struct RedBlackNode * result = Find( X, left, NullNode );
            /*@
			if (result == NullNode) {
			  close subtree(T, NullNode);
			} else {
			  open subtree(result, NullNode); // To obtain distinctness.
			  close subtree(result, NullNode);
			  close tseg(T, NullNode, result, X);
		    }
		    @*/
            return result;
        } else {
            int element = T->Element;
            if( element < X ) {
                struct RedBlackNode * right = T->Right;
                struct RedBlackNode * result = Find( X, right, NullNode );
				/*@
                if (result == NullNode) {
				  close subtree(T, NullNode);
			    } else {
				  open subtree(result, NullNode); // To obtain result != T
				  close subtree(result, NullNode);
				  close tseg(T, NullNode, result, X);
			    }
				@*/
                return result;
            } else {
                //@ close subtree(T, NullNode);
                return T;
            }
        }
    }
}

struct RedBlackNode *
FindMin( struct RedBlackNode * T, struct RedBlackNode * NullNode )
{
    T = T->Right;
    struct RedBlackNode * left = T->Left;
    while( left != NullNode )
      //@ invariant true;
    {
        T = T->Left;
        left = T->Left;
    }

    return T;
}

struct RedBlackNode *
FindMax( struct RedBlackNode * T, struct RedBlackNode * NullNode )
{
    struct RedBlackNode * right = T->Right;
    while( right != NullNode )
      //@ invariant true;
    {
        T = T->Right;
        right = T->Right;
    }

    return T;
}

/* This function can be called only if K2 has a left child */
/* Perform a rotate between a node (K2) and its left child */
/* Update heights, then return new root */

struct RedBlackNode *
SingleRotateWithLeft( struct RedBlackNode * K2, struct RedBlackNode * NullNode )
  //@ requires K2->Left |-> ?k1 &*& k1->Right |-> ?k1_right;
  //@ ensures K2->Left |-> k1_right &*& k1->Right |-> K2 &*& result == k1;
{
    struct RedBlackNode * K1 = K2->Left;
    struct RedBlackNode * right = K1->Right;
    K2->Left = right;
    K1->Right = K2;

    return K1;  /* New root */
}

/* This function can be called only if K1 has a right child */
/* Perform a rotate between a node (K1) and its right child */
/* Update heights, then return new root */

struct RedBlackNode *
SingleRotateWithRight( struct RedBlackNode * K1, struct RedBlackNode * NullNode )
  //@ requires K1->Right |-> ?k2 &*& k2->Left |-> ?k2_left;
  //@ ensures K1->Right |-> k2_left &*& k2->Left |-> K1 &*& result == k2;
{
    struct RedBlackNode * K2 = K1->Right;
    struct RedBlackNode * left = K2->Left;
    K1->Right = left;
    K2->Left = K1;

    return K2;  /* New root */
}

/* Perform a rotation at node X */
/* (whose parent is passed as a parameter) */
/* The child is deduced by examining Item */

/*@
predicate node(struct RedBlackNode * n, int elem, struct RedBlackNode * left, struct RedBlackNode * right)
  requires n->Element |-> elem &*& n->Left |-> left &*& n->Right |-> right &*& n->Color |-> _ &*& malloc_block_RedBlackNode(n);
@*/

struct RedBlackNode *
Rotate( int Item, struct RedBlackNode * Parent, struct RedBlackNode * NullNode )
  /*@ requires
        node(Parent, ?elem, ?left, ?right)
		&*& Item < elem
		    ? node(left, ?leftElem, ?leftLeft, ?leftRight)
			  &*& Item < leftElem
			      ? node(leftLeft, ?leftLeftElem, ?leftLeftLeft, ?leftLeftRight)
				  : node(leftRight, ?leftRightElem, ?leftRightLeft, ?leftRightRight)
		    : node(right, ?rightElem, ?rightLeft, ?rightRight)
			  &*& Item < rightElem
			      ? node(rightLeft, ?rightLeftElem, ?rightLeftLeft, ?rightLeftRight)
				  : node(rightRight, ?rightRightElem, ?rightRightLeft, ?rightRightRight);
  @*/
  /*@ ensures
        Item < elem
		? Item < leftElem
		  ? node(Parent, elem, leftLeft, right) &*& node(leftLeft, leftLeftElem, leftLeftLeft, left) &*& node(left, leftElem, leftLeftRight, leftRight)
		  : node(Parent, elem, leftRight, right) &*& node(leftRight, leftRightElem, left, leftRightRight) &*& node(left, leftElem, leftLeft, leftRightLeft)
        : Item < rightElem
		  ? node(Parent, elem, left, rightLeft) &*& node(rightLeft, rightLeftElem, rightLeftLeft, right) &*& node(right, rightElem, rightLeftRight, rightRight)
		  : node(Parent, elem, left, rightRight) &*& node(rightRight, rightRightElem, right, rightRightRight) &*& node(right, rightElem, rightLeft, rightRightLeft);
  @*/
{
	//@ open node(Parent, _, _, _);
    int element = Parent->Element;
    if( Item < element ) {
        struct RedBlackNode * left = Parent->Left;
		//@ open node(left, _, _, _);
        int leftElement = left->Element;
        if (Item < leftElement) {
			//@ open node(leftLeft, _, _, _);
            struct RedBlackNode * result = SingleRotateWithLeft( left, NullNode );
            Parent->Left = result;
			//@ close node(Parent, elem, leftLeft, right);
			//@ close node(leftLeft, leftLeftElem, leftLeftLeft, left);
			//@ close node(left, leftElem, leftLeftRight, leftRight);
            return result;
        } else {
			//@ open node(leftRight, _, _, _);
            struct RedBlackNode * result = SingleRotateWithRight( left, NullNode );
            Parent->Left = result;
		    //@ close node(Parent, elem, leftRight, right);
		    //@ close node(leftRight, leftRightElem, left, leftRightRight);
		    //@ close node(left, leftElem, leftLeft, leftRightLeft);
            return result;
        }
    } else {
		//@ open node(right, _, _, _);
	    struct RedBlackNode * right = Parent->Right;
		int element = right->Element;
        if (Item < element) {
			//@ open node(rightLeft, _, _, _);
            struct RedBlackNode * result = SingleRotateWithLeft( right, NullNode );
            Parent->Right = result;
			//@ close node(Parent, elem, left, rightLeft);
			//@ close node(rightLeft, rightLeftElem, rightLeftLeft, right);
			//@ close node(right, rightElem, rightLeftRight, rightRight);
            return result;
        } else {
			//@ open node(rightRight, _, _, _);
            struct RedBlackNode * result = SingleRotateWithRight( right, NullNode );
            Parent->Right = result;
			//@ close node(Parent, elem, left, rightRight);
			//@ close node(rightRight, rightRightElem, right, rightRightRight);
			//@ close node(right, rightElem, rightLeft, rightRightLeft);
            return result;
        }
    }
}

void HandleReorient( int Item, struct RedBlackNode * T, struct RedBlackNode * X, struct RedBlackNode * P, struct RedBlackNode * GP, struct RedBlackNode * GGP, struct RedBlackNode * NullNode )
{
    X->Color = (0 /* Red */);        /* Do the color flip */
    struct RedBlackNode * left = X->Left;
    left->Color = (1 /* Black */);
    struct RedBlackNode * right = X->Right;
    right->Color = (1 /* Black */);

    int p_color = P->Color;
    if( p_color == (0 /* Red */) )  /* Have to rotate */
    {
        GP->Color = (0 /* Red */);
        struct RedBlackNode * gp_element = GP->Element;
        struct RedBlackNode * p_element = P->Element;
        if( (Item < gp_element) != (Item < p_element) ) {
            P = Rotate( Item, GP );  /* Start double rotate */
        } else {
        }
        X = Rotate( Item, GGP, NullNode );
        X->Color = (1 /* Black */);
    }
    else
    {
    }
    struct RedBlackNode * t_right = T->Right;
    t_right->Color = (1 /* Black */);  /* Make root black */
}

struct RedBlackNode *
Insert( int Item, struct RedBlackNode * T, struct RedBlackNode * X, struct RedBlackNode * NullNode )
{
    struct RedBlackNode * X = T;
    struct RedBlackNode * G = T;
    struct RedBlackNode * P = T;
    struct RedBlackNode * GP = T;
    struct RedBlackNode * GGP = 0;
    NullNode->Element = Item;
    struct RedBlackNode * x_element = X->Element;
    while( X->Element != Item )  /* Descend down the tree */
      //@ invariant true;
    {
        GGP = GP;
        GP = P;
        P = X;
        if( Item < x_element ) {
            X = X->Left;
        } else {
            X = X->Right;
        }
        struct RedBlackNode * x_left = X->Left;
        int x_left_color = x_left->Color;
        struct RedBlackNode * x_right = X->Right;
        int x_right_color = x_right->Color;
        if( x_left_color == (0 /* Red */) && x_right_color == (0 /* Red */) ) {
            HandleReorient( Item, T, P, GP, GGP, NullNode );
        } else {
        }
        x_element = X->Element;
    }

    if( X != NullNode ) {
        return NullNode;  /* Duplicate */
    } else {
    }

    X = malloc( sizeof( struct RedBlackNode ) );
    X->Element = Item;
    X->Left = NullNode;
    X->Right = NullNode;

    struct RedBlackNode * p_element = P->Element;
    if( Item < p_element ) { /* Attach to its parent */
        P->Left = X;
    } else {
        P->Right = X;
    }
    HandleReorient( Item, T, NullNode ); /* Color it red; maybe rotate */

    return T;
}
