// verifast_options{ignore_unwind_paths}

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

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

fix node_count(tree: tree) -> i32 {
    match tree {
        empty(node) => 1,
        nonempty(node, left, right) => 1 + node_count(left) + node_count(right)
    }
}

fix tree_root(tree: tree) -> *mut Tree {
    match tree {
        empty(node) => node,
        nonempty(node, left, right) => node
    }
}

lem_auto node_count_positive(tree: tree)
    req true;
    ens node_count(tree) >= 1;
{
    match tree {
        empty(node) => {}
        nonempty(node, left, right) => {
            node_count_positive(left);
            node_count_positive(right);
        }
    }
}

pred Tree(node: *mut Tree, marked: bool; parent: *mut Tree, shape: tree) =
    node != 0 &*&
    alloc_block_Tree(node) &*&
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

lem_auto Tree_inv()
    req Tree(?node, ?marked, ?parent, ?shape);
    ens Tree(node, marked, parent, shape) &*& node != 0 &*& node == tree_root(shape);
{
    open Tree(node, marked, parent, shape);
    close Tree(node, marked, parent, shape);
}

pred stack(parent: *mut Tree, current: *mut Tree, cShape: tree, root: *mut Tree, rootShape: tree, stepsLeft: i32) =
    current != 0 &*&
    if parent == 0 {
        root == current &*&
        rootShape == cShape &*&
        stepsLeft == 0
    } else {
        parent != 0 &*&
        alloc_block_Tree(parent) &*&
        (*parent).left |-> ?left &*&
        (*parent).right |-> ?right &*&
        (*parent).mark |-> true &*&
        (*parent).parent |-> current &*&
        exists::<bool>(?currentIsLeftChild) &*&
        if currentIsLeftChild {
            Tree(left, false, parent, ?rightShape) &*& left != 0 &*&
            stack(right, parent, nonempty(parent, cShape, rightShape), root, rootShape, ?stepsLeft1) &*&
            stepsLeft1 >= 0 &*&
            stepsLeft == node_count(rightShape) * 2 + 1 + stepsLeft1
        } else {
            Tree(right, true, parent, ?leftShape) &*& right != 0 &*&
            stack(left, parent, nonempty(parent, leftShape, cShape), root, rootShape, ?stepsLeft1) &*&
            stepsLeft1 >= 0 &*& stepsLeft == 1 + stepsLeft1
        }
    };

pred inv_(xIsNew: bool, x: *mut Tree, root: *mut Tree, rootShape: tree, stepsLeft: i32) =
    if xIsNew {
        Tree(x, false, ?parent, ?xShape) &*& stack(parent, x, xShape, root, rootShape, ?stepsLeft1) &*&
        stepsLeft1 >= 0 &*& stepsLeft == node_count(xShape) * 2 - 1 + stepsLeft1
    } else {
        stack(x, ?child, ?childShape, root, rootShape, stepsLeft) &*& stepsLeft >= 0 &*&
        Tree(child, true, x, childShape)
    };

@*/

impl Tree {

    unsafe fn new_with_children(left: *mut Tree, right: *mut Tree) -> *mut Tree
    //@ req Tree(left, false, _, ?leftShape) &*& Tree(right, false, _, ?rightShape);
    //@ ens Tree(result, false, 0, nonempty(result, leftShape, rightShape));
    {
        let result = alloc(Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Tree>());
        }
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
        let result = alloc(Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Tree>());
        }
        (*result).left = std::ptr::null_mut();
        (*result).right = std::ptr::null_mut();
        (*result).parent = std::ptr::null_mut();
        (*result).mark = false;
        result
    }

    unsafe fn mark(root: *mut Tree)
    //@ req Tree(root, false, 0, ?rootShape);
    //@ ens Tree(root, true, 0, rootShape);
    {
        let mut x = root;
        //@ Tree_inv();
        //@ close stack(0, root, rootShape, root, rootShape, 0);
        //@ close inv_(true, x, root, rootShape, _);
        loop {
            //@ inv inv_(?xIsNew, x, root, rootShape, ?stepsLeft) &*& x != 0;
            //@ open inv_(_, _, _, _, _);
            //@ if xIsNew == false { open stack(x, _, _, _, _, _); }
            (*x).mark = true;
            if (*x).left.is_null() && (*x).right.is_null() {
                x = (*x).parent;
                //@ close inv_(false, x, root, rootShape, _);
            } else {
                let y = (*x).left;
                (*x).left = (*x).right;
                (*x).right = (*x).parent;
                (*x).parent = y;
                /*@
                if xIsNew {
                    assert Tree(y, false, x, ?leftShape);
                    close exists(true);
                    close stack(x, y, leftShape, root, rootShape, ?stepsLeft1);
                    close inv_(true, y, root, rootShape, _);
                } else {
                    open exists(?markedLeftSubtree);
                    if markedLeftSubtree {
                        close exists(false);
                        assert Tree(y, false, x, ?rightShape);
                        Tree_inv();
                        close stack(x, y, rightShape, root, rootShape, _);
                        close inv_(true, y, root, rootShape, _);
                    } else {
                        close inv_(false, y, root, rootShape, _);
                    }
                }
                @*/
                x = y;
            }
            if x.is_null() {
                break;
            }
            //@ assert inv_(_, _, _, _, ?stepsLeft1) &*& stepsLeft1 < stepsLeft;
        }
        //@ open inv_(_, _, _, _, _);
        //@ open stack(_, _, _, _, _, _);
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree, _, _, _);
    //@ ens true;
    {
        if !(*tree).left.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
        }
        dealloc(tree as *mut u8, Layout::new::<Tree>());
    }

}

fn main() {
    unsafe {
        let left_child = Tree::new();
        let right_child = Tree::new();
        let root = Tree::new_with_children(left_child, right_child);

        Tree::mark(root);
        assert((*root).mark);
        assert((*left_child).mark);
        assert((*right_child).mark);
        //@ close Tree(root, true, _, _);
        Tree::dispose(root);
    }
}
