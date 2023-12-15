struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    parent: *mut Tree,
    mark: bool
}

/*@

pred Tree(node: *mut Tree, marked: bool; parent: *mut Tree) =
    node != 0 &*&
    alloc_block(node, std::mem::size_of::<Tree>()) &*&
    struct_Tree_padding(node) &*&
    (*node).left |-> ?left &*&
    (*node).right |-> ?right &*&
    (*node).mark |-> ?mark &*& if marked { mark } else { true } &*&
    (*node).parent |-> parent &*&
    if left == 0 {
        right == 0
    } else {
        right != 0 &*&
        Tree(left, marked, node) &*&
        Tree(right, marked, node)
    };

lem Tree_inv()
    req Tree(?node, ?marked, ?parent);
    ens Tree(node, marked, parent) &*& node != 0;
{
    open Tree(node, marked, parent);
    close Tree(node, marked, parent);
}

pred stack(parent: *mut Tree, current: *mut Tree, root: *mut Tree) =
    current != 0 &*&
    if parent == 0 {
        root == current
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
            Tree(left, false, parent) &*& left != 0 &*&
            stack(right, parent, root)
        } else {
            Tree(right, true, parent) &*& right != 0 &*&
            stack(left, parent, root)
        }
    };

pred inv_(xIsNew: bool, x: *mut Tree, root: *mut Tree) =
    if xIsNew {
        Tree(x, false, ?parent) &*& stack(parent, x, root)
    } else {
        stack(x, ?child, root) &*& Tree(child, true, x)
    };

@*/

impl Tree {

    unsafe fn new_with_children(left: *mut Tree, right: *mut Tree) -> *mut Tree
    //@ req Tree(left, false, _) &*& Tree(right, false, _);
    //@ ens Tree(result, false, 0);
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
    //@ ens Tree(result, false, 0);
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
    //@ req Tree(root, false, 0);
    //@ ens Tree(root, true, 0);
    {
        Self::mark0(root, root);
    }

    unsafe fn mark0(root: *mut Tree, mut x: *mut Tree)
    //@ req Tree(root, false, 0) &*& x == root;
    //@ ens Tree(root, true, 0);
    {
        //@ Tree_inv();
        //@ close stack(0, root, root);
        //@ close inv_(true, x, root);
        loop {
            //@ inv inv_(?xIsNew, x, root) &*& x != 0;
            //@ open inv_(_, _, _);
            //@ if xIsNew == false { open stack(x, _, _); }
            (*x).mark = true;
            if (*x).left.is_null() && (*x).right.is_null() {
                x = (*x).parent;
                //@ close inv_(false, x, root);
            } else {
                let y = (*x).left;
                (*x).left = (*x).right;
                (*x).right = (*x).parent;
                (*x).parent = y;
                /*@
                if xIsNew {
                    assert Tree(y, false, x);
                    close exists(true);
                    close stack(x, y, root);
                    close inv_(true, y, root);
                } else {
                    open exists(?markedLeftSubtree);
                    if markedLeftSubtree {
                        close exists(false);
                        assert Tree(y, false, x);
                        Tree_inv();
                        close stack(x, y, root);
                        close inv_(true, y, root);
                    } else {
                        close inv_(false, y, root);
                    }
                }
                @*/
                x = y;
            }
            if x.is_null() {
                break;
            }
        }
        //@ open inv_(_, _, _);
        //@ open stack(_, _, _);
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree, _, _);
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
        if !(*root).mark {
            (*(*root).parent).parent = std::ptr::null_mut(); // Null dereference
        }
        //@ close Tree(root, true, _);
        Tree::dispose(root);
    }
}
