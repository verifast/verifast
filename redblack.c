/* typedef enum ColorType { Red = 0, Black = 1 } ColorType; */

struct RedBlackNode
{
    int  Element;
    struct RedBlackNode * Left;
    struct RedBlackNode * Right;
    int    Color;
};

/*@
predicate tree(struct RedBlackNode * root, struct RedBlackNode * NullNode)
  requires root->Element |-> _ &*& root->Left |-> ?l &*& root->Right |-> ?r &*& root->Color |-> _ &*& malloc_block_RedBlackNode(root)
    &*& (l == NullNode ? emp : tree(l, NullNode)) &*& (r == NullNode ? emp : tree(r, NullNode));
@*/

struct RedBlackNode *
MakeNullNode()
  //@ requires emp;
  //@ ensures tree(result, result);
{
    struct RedBlackNode *NullNode = malloc( sizeof( struct RedBlackNode ) );
    NullNode->Left = NullNode;
    NullNode->Right = NullNode;
    NullNode->Color = (1 /* Black */);
    NullNode->Element = 12345;
    //@ close tree(NullNode, NullNode);
    return NullNode;
}

struct RedBlackNode *
MakeRootNode(struct RedBlackNode * NullNode)
  //@ requires tree(NullNode, NullNode);
  //@ ensures tree(result, NullNode) &*& tree(NullNode, NullNode);
{
    /* Create the header node */
    struct RedBlackNode * T = malloc( sizeof( struct RedBlackNode ) );
    /* To prove disjointness */
    //@ open tree(NullNode, NullNode);
    //@ close tree(NullNode, NullNode);
    T->Element = (0 - 10000);
    T->Left = NullNode;
    T->Right = NullNode;
    T->Color = (1 /* Black */);
    //@ close tree(T, NullNode);
    return T;
}

/* Print the tree, watch out for NullNode, */
/* and skip header */

void
DoPrint( struct RedBlackNode * T, struct RedBlackNode * NullNode )
  //@ requires T == NullNode ? emp : tree(T, NullNode);
  //@ ensures T == NullNode ? emp : tree(T, NullNode);
{
    if( T != NullNode )
    {
        //@ open tree(T, NullNode);
        struct RedBlackNode * left = T->Left;
        DoPrint( left, NullNode );
        // Output( T->Element );
        struct RedBlackNode * right = T->Right;
        DoPrint( right, NullNode );
        //@ close tree(T, NullNode);
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
  //@ requires T == NullNode ? emp : tree(T, NullNode);
  //@ ensures emp &*& result == NullNode;
{
    if( T != NullNode )
    {
        //@ open tree(T, NullNode);
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
          &*& (r == NullNode ? emp : tree(r, NullNode))
        : (l == NullNode ? emp : tree(l, NullNode))
          &*& (r == hole ? emp : tseg(r, NullNode, hole, holeValue));
@*/

// Returns the node containing value X, or NullNode if X is not in the tree.

struct RedBlackNode *
Find( int X, struct RedBlackNode * T, struct RedBlackNode * NullNode )
  //@ requires T == NullNode ? emp : tree(T, NullNode);
  //@ ensures T == NullNode ? result == NullNode : result == NullNode ? tree(T, NullNode) : result == T ? tree(result, NullNode) : tseg(T, NullNode, result, X) &*& tree(result, NullNode);
{
    if( T == NullNode ) {
        return NullNode;
    } else {
        //@ open tree(T, NullNode);
        int element = T->Element;
        if( X < element ) {
            struct RedBlackNode * left = T->Left;
            struct RedBlackNode * result = Find( X, left, NullNode );
            //@ if (left == NullNode) { close tree(T, NullNode); } else { close tseg(T, NullNode, result, X); }
            return result;
        } else {
            int element = T->Element;
            if( element < X ) {
                struct RedBlackNode * right = T->Right;
                struct RedBlackNode * result = Find( X, right, NullNode );
                //@ if (right == NullNode) { close tree(T, NullNode); } else { close tseg(T, NullNode, result, X); }
                return result;
            } else {
                //@ close tree(T, NullNode);
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

struct RedBlackNode *
Rotate( int Item, struct RedBlackNode * Parent, struct RedBlackNode * NullNode )
{
    int element = Parent->Element;
    if( Item < element ) {
        struct RedBlackNode * left = Parent->Left;
        int leftElement = left->Element;
        if (Item < leftElement) {
            struct RedBlackNode * result = SingleRotateWithLeft( leftElement, NullNode );
            Parent->Left = result;
            return result;
        } else {
            struct RedBlackNode * result = SingleRotateWithRight( leftElement, NullNode );
            Parent->Left = result;
            return result;
        }
    } else {
        if (Item < Parent->Right->Element) {
            struct RedBlackNode * result = SingleRotateWithLeft( Parent->Right, NullNode );
            Parent->Right = result;
            return result;
        } else {
            struct RedBlackNode * result = SingleRotateWithRight( Parent->Right, NullNode );
            Parent->Right = result;
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
