// typedef enum ColorType { Red = 0, Black = 1 } ColorType;

struct RedBlackNode
{
    int  Element;
    struct RedBlackNode * Left;
    struct RedBlackNode * Right;
    int    Color;
};

static struct RedBlackNode * NullNode = NULL;  /* Needs initialization */

/* Initialization procedure */
struct RedBlackNode *
Initialize( void )
{
    struct RedBlackNode * T;

    if( NullNode == NULL )
    {
        NullNode = malloc( sizeof( struct RedBlackNode ) );
        if( NullNode == NULL )
            FatalError( "Out of space!!!" );
        NullNode->Left = NullNode->Right = NullNode;
        NullNode->Color = (1 /* Black */);
        NullNode->Element = 12345;
    }

    /* Create the header node */
    T = malloc( sizeof( struct RedBlackNode ) );
    if( T == NULL )
        FatalError( "Out of space!!!" );
    T->Element = (-10000);
    T->Left = T->Right = NullNode;
    T->Color = (1 /* Black */);

    return T;
}

void
Output( int Element )
{
    printf( "%d\n", Element );
}

/* Print the tree, watch out for NullNode, */
/* and skip header */

static void
DoPrint( struct RedBlackNode * T )
{
    if( T != NullNode )
    {
        DoPrint( T->Left );
        Output( T->Element );
        DoPrint( T->Right );
    }
}

void
PrintTree( struct RedBlackNode * T )
{
    DoPrint( T->Right );
}

static struct RedBlackNode *
MakeEmptyRec( struct RedBlackNode * T )
{
    if( T != NullNode )
    {
        MakeEmptyRec( T->Left );
        MakeEmptyRec( T->Right );
        free( T );
    }
    return NullNode;
}

struct RedBlackNode *
MakeEmpty( struct RedBlackNode * T )
{
    T->Right = MakeEmptyRec( T->Right );
    return T;
}

struct RedBlackNode *
Find( int X, struct RedBlackNode * T )
{
    if( T == NullNode )
        return NullNode;
    if( X < T->Element )
        return Find( X, T->Left );
    else
    if( X > T->Element )
        return Find( X, T->Right );
    else
        return T;
}

struct RedBlackNode *
FindMin( struct RedBlackNode * T )
{
    T = T->Right;
    while( T->Left != NullNode )
        T = T->Left;

    return T;
}

struct RedBlackNode *
FindMax( struct RedBlackNode * T )
{
    while( T->Right != NullNode )
        T = T->Right;

    return T;
}

/* This function can be called only if K2 has a left child */
/* Perform a rotate between a node (K2) and its left child */
/* Update heights, then return new root */

static struct RedBlackNode *
SingleRotateWithLeft( struct RedBlackNode * K2 )
{
    struct RedBlackNode * K1;

    K1 = K2->Left;
    K2->Left = K1->Right;
    K1->Right = K2;

    return K1;  /* New root */
}

/* This function can be called only if K1 has a right child */
/* Perform a rotate between a node (K1) and its right child */
/* Update heights, then return new root */

static struct RedBlackNode *
SingleRotateWithRight( struct RedBlackNode * K1 )
{
    struct RedBlackNode * K2;

    K2 = K1->Right;
    K1->Right = K2->Left;
    K2->Left = K1;

    return K2;  /* New root */
}

/* Perform a rotation at node X */
/* (whose parent is passed as a parameter) */
/* The child is deduced by examining Item */

static struct RedBlackNode *
Rotate( int Item, struct RedBlackNode * Parent )
{

    if( Item < Parent->Element )
        return Parent->Left = Item < Parent->Left->Element ?
            SingleRotateWithLeft( Parent->Left ) :
            SingleRotateWithRight( Parent->Left );
    else
        return Parent->Right = Item < Parent->Right->Element ?
            SingleRotateWithLeft( Parent->Right ) :
            SingleRotateWithRight( Parent->Right );
}

static struct RedBlackNode * X, P, GP, GGP;

static
void HandleReorient( int Item, struct RedBlackNode * T )
{
    X->Color = (0 /* Red */);        /* Do the color flip */
    X->Left->Color = (1 /* Black */);
    X->Right->Color = (1 /* Black */);

    if( P->Color == (0 /* Red */) )  /* Have to rotate */
    {
        GP->Color = (0 /* Red */);
        if( (Item < GP->Element) != (Item < P->Element) )
            P = Rotate( Item, GP );  /* Start double rotate */
        X = Rotate( Item, GGP );
        X->Color = (1 /* Black */);
    }
    T->Right->Color = (1 /* Black */);  /* Make root black */
}

struct RedBlackNode *
Insert( int Item, struct RedBlackNode * T )
{
    X = P = GP = T;
    NullNode->Element = Item;
    while( X->Element != Item )  /* Descend down the tree */
    {
        GGP = GP; GP = P; P = X;
        if( Item < X->Element )
            X = X->Left;
        else
            X = X->Right;
        if( X->Left->Color == (0 /* Red */) && X->Right->Color == (0 /* Red */) )
            HandleReorient( Item, T );
    }

    if( X != NullNode )
        return NullNode;  /* Duplicate */

    X = malloc( sizeof( struct RedBlackNode ) );
    if( X == NULL )
        FatalError( "Out of space!!!" );
    X->Element = Item;
    X->Left = X->Right = NullNode;

    if( Item < P->Element )  /* Attach to its parent */
        P->Left = X;
    else
        P->Right = X;
    HandleReorient( Item, T ); /* Color it red; maybe rotate */

    return T;
}

struct RedBlackNode *
Remove( int Item, struct RedBlackNode * T )
{
    printf( "Remove is unimplemented\n" );
    if( Item )
        return T;
    return T;
}

int
Retrieve( struct RedBlackNode * P )
{
    return P->Element;
}

