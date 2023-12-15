unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    parent: *mut Tree,
    mark: bool
}

/*@

inductive tree = empty(node: *mut Tree) | nonempty(node: *mut Tree, left: tree, right: tree);

pred Tree(node: *mut Tree, marked: bool; parent: *mut Tree, shape: tree) =
    node != 0 &*&
    alloc_block(node, std::mem::size_of::<Tree>()) &*&
    struct_Tree_padding(node) &*&
    (*node).left |-> ?left &*&
    (*node).right |-> ?right &*&
    (*node).mark |-> ?mark &*& if marked { mark } else { true } &*&
    (*node).parent |-> parent &*&
    if left == 0 {
        right == 0 &*&
        shape == empty(node)
    } else {
        right != 0 &*&
        Tree(left, marked, node, ?leftShape) &*&
        Tree(right, marked, node, ?rightShape) &*&
        shape == nonempty(node, leftShape, rightShape)
    };

lem Tree_inv()
    req Tree(?node, ?marked, ?parent, ?shape);
    ens Tree(node, marked, parent, shape) &*& node != 0;
{
    open Tree(node, marked, parent, shape);
    close Tree(node, marked, parent, shape);
}

pred stack(parent: *mut Tree, current: *mut Tree, cShape: tree, root: *mut Tree, rootShape: tree) =
    current != 0 &*&
    if parent == 0 {
        root == current &*&
        rootShape == cShape
    } else {
        parent != 0 &*&
        alloc_block(parent, std::mem::size_of::<Tree>()) &*&
        struct_Tree_padding(parent) &*&
        (*parent).left |-> ?left &*&
        (*parent).right |-> ?right &*&
        (*parent).mark |-> true &*&
        (*parent).parent |-> current &*&
        exists::<bool>(?currentIsLeftChild) &*&
        if currentIsLeftChild {
            Tree(left, false, parent, ?rightShape) &*& left != 0 &*&
            stack(right, parent, nonempty(parent, cShape, rightShape), root, rootShape)
        } else {
            Tree(right, true, parent, ?leftShape) &*& right != 0 &*&
            stack(left, parent, nonempty(parent, leftShape, cShape), root, rootShape)
        }
    };

pred inv_(xIsNew: bool, x: *mut Tree, root: *mut Tree, rootShape: tree) =
    if xIsNew {
        Tree(x, false, ?parent, ?xShape) &*& stack(parent, x, xShape, root, rootShape)
    } else {
        stack(x, ?child, ?childShape, root, rootShape) &*& Tree(child, true, x, childShape)
    };

@*/

impl Tree {

    unsafe fn new_with_children(left: *mut Tree, right: *mut Tree) -> *mut Tree
    //@ req Tree(left, false, _, ?leftShape) &*& Tree(right, false, _, ?rightShape);
    //@ ens Tree(result, false, 0, nonempty(result, leftShape, rightShape));
    {
        let result = std::alloc::alloc(std::alloc::Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Tree>());
        }
        //@ close_struct(result);
        (*result).left = left;
        (*left).parent = result;
        (*result).right = right;
        (*right).parent = result;
        (*result).parent = std::ptr::null_mut();
        (*result).mark = false;
        result
    }

    unsafe fn new() -> *mut Tree
    //@ req true;
    //@ ens Tree(result, false, 0, empty(result));
    {
        let result = std::alloc::alloc(std::alloc::Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Tree>());
        }
        //@ close_struct(result);
        (*result).left = std::ptr::null_mut();
        (*result).right = std::ptr::null_mut();
        (*result).parent = std::ptr::null_mut();
        (*result).mark = false;
        result
    }

    unsafe fn mark(root: *mut Tree)
    //@ req Tree(root, false, 0, ?shape);
    //@ ens Tree(root, true, 0, shape);
    {
        Self::mark0(root, root);
    }

    unsafe fn mark0(root: *mut Tree, mut x: *mut Tree)
    //@ req Tree(root, false, 0, ?rootShape) &*& x == root;
    //@ ens Tree(root, true, 0, rootShape);
    {
        //@ Tree_inv();
        //@ close stack(0, root, rootShape, root, rootShape);
        //@ close inv_(true, x, root, rootShape);
        loop {
            //@ inv inv_(?xIsNew, x, root, rootShape) &*& x != 0;
            //@ open inv_(_, _, _, _);
            //@ if xIsNew == false { open stack(x, _, _, _, _); }
            (*x).mark = true;
            if (*x).left.is_null() && (*x).right.is_null() {
                x = (*x).parent;
                //@ close inv_(false, x, root, rootShape);
            } else {
                let y = (*x).left;
                (*x).left = (*x).right;
                (*x).right = (*x).parent;
                (*x).parent = y;
                /*@
                if xIsNew {
                    assert Tree(y, false, x, ?leftShape);
                    close exists(true);
                    close stack(x, y, leftShape, root, rootShape);
                    close inv_(true, y, root, rootShape);
                } else {
                    open exists(?markedLeftSubtree);
                    if markedLeftSubtree {
                        close exists(false);
                        assert Tree(y, false, x, ?rightShape);
                        Tree_inv();
                        close stack(x, y, rightShape, root, rootShape);
                        close inv_(true, y, root, rootShape);
                    } else {
                        close inv_(false, y, root, rootShape);
                    }
                }
                @*/
                x = y;
            }
            if x.is_null() {
                break;
            }
        }
        //@ open inv_(_, _, _, _);
        //@ open stack(_, _, _, _, _);
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree, _, _, _);
    //@ ens true;
    {
        if !(*tree).left.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
        }
        //@ open_struct(tree);
        std::alloc::dealloc(tree as *mut u8, std::alloc::Layout::new::<Tree>());
    }

}

fn main() {
    unsafe {
        let left_child = Tree::new();
        let right_child = Tree::new();
        let root = Tree::new_with_children(left_child, right_child);

        Tree::mark(root);
        assert((*root).mark);
        //@ close Tree(root, true, _, _);
        Tree::dispose(root);
    }
}
