/*@

lem_auto bitand_zero(y: usize)
    req true;
    ens 0 & y == 0;
{
    assume(false);
}

lem set_lsb(x: *mut u8)
    req x as usize & 1 == 0;
    ens (x + 1) as usize & 1 == 1;
{
    assume(false);
}

lem clear_lsb(x: *mut u8)
    req x as usize & 1 != 0;
    ens (x - 1) as usize & 1 == 0;
{
    assume(false);
}

@*/

unsafe fn assert(_b: bool)
//@ req _b;
//@ ens true;
{}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    parent: *mut Tree,
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

pred Tree(node: *mut Tree; parent: *mut Tree, shape: tree) =
    node != 0 &*&
    alloc_block(node, std::mem::size_of::<Tree>()) &*&
    struct_Tree_padding(node) &*&
    node as usize & 1 == 0 &*&
    pointer_within_limits(node as *mut u8 + 1) == true &*&
    (*node).left |-> ?left &*&
    (*node).right |-> ?right &*&
    (*node).parent |-> parent &*&
    parent as usize & 1 == 0 &*&
    pointer_within_limits(parent as *mut u8 + 1) == true &*&
    if left == 0 {
        right == 0 &*&
        shape == empty(node)
    } else {
        right != 0 &*&
        Tree(left, node, ?leftShape) &*&
        Tree(right, node, ?rightShape) &*&
        shape == nonempty(node, leftShape, rightShape)
    };

lem_auto Tree_inv()
    req Tree(?node, ?parent, ?shape);
    ens Tree(node, parent, shape) &*& node != 0 &*& node == tree_root(shape) &*&
        node as usize & 1 == 0 &*& pointer_within_limits(node as *mut u8 + 1) == true &*&
        parent as usize & 1 == 0 &*& pointer_within_limits(parent as *mut u8 + 1) == true;
{
    open Tree(node, parent, shape);
    close Tree(node, parent, shape);
}

pred stack(parent: *mut Tree, current: *mut Tree, cShape: tree, root: *mut Tree, rootShape: tree, stepsLeft: i32, countTodo: i32) =
    current != 0 &*&
    if parent == 0 {
        root == current &*&
        rootShape == cShape &*&
        stepsLeft == 0 &*&
        countTodo == 0
    } else {
        alloc_block(parent, std::mem::size_of::<Tree>()) &*&
        struct_Tree_padding(parent) &*&
        parent as usize & 1 == 0 &*&
        pointer_within_limits(parent as *mut u8 + 1) == true &*&
        (*parent).left |-> ?left &*&
        (*parent).right |-> ?right &*&
        (*parent).parent |-> current &*&
        if right as usize & 1 != 0 {
            pointer_within_limits(right as *mut u8 - 1) == true &*&
            Tree(left, parent, ?rightShape) &*& left != 0 &*&
            stack((right as *mut u8 - 1) as *mut Tree, parent, nonempty(parent, cShape, rightShape), root, rootShape, ?stepsLeft1, ?countTodo0) &*&
            stepsLeft1 >= 0 &*& countTodo0 >= 0 &*&
            stepsLeft == node_count(rightShape) * 2 + 1 + stepsLeft1 &*&
            countTodo == countTodo0 + node_count(rightShape)
        } else {
            left as usize & 1 != 0 &*&
            pointer_within_limits(left as *mut u8 - 1) == true &*&
            Tree(right, parent, ?leftShape) &*& right != 0 &*&
            stack((left as *mut u8 - 1) as *mut Tree, parent, nonempty(parent, leftShape, cShape), root, rootShape, ?stepsLeft1, countTodo) &*&
            stepsLeft1 >= 0 &*& stepsLeft == 1 + stepsLeft1
        }
    };

pred inv_(x_is_new: bool, x: *mut Tree, root: *mut Tree, rootShape: tree, stepsLeft: i32, countTodo: i32) =
    if x_is_new {
        Tree(x, ?parent, ?xShape) &*& stack(parent, x, xShape, root, rootShape, ?stepsLeft1, ?countTodo0) &*&
        stepsLeft1 >= 0 &*& stepsLeft == node_count(xShape) * 2 - 1 + stepsLeft1 &*&
        countTodo0 >= 0 &*&
        countTodo == node_count(xShape) + countTodo0
    } else {
        stack(x, ?child, ?childShape, root, rootShape, stepsLeft, countTodo) &*& stepsLeft >= 0 &*& countTodo >= 0 &*&
        Tree(child, x, childShape)
    };

fn_type TreeVisitor(p: pred(*mut u8, i32)) = unsafe fn(data: *mut u8, node: *mut Tree);
    req p(data, ?countTodo) &*& 0 < countTodo;
    ens p(data, countTodo - 1);

@*/

type TreeVisitor = unsafe fn(data: *mut u8, node: *mut Tree);

impl Tree {

    unsafe fn new_with_children(left: *mut Tree, right: *mut Tree) -> *mut Tree
    //@ req Tree(left, _, ?leftShape) &*& Tree(right, _, ?rightShape);
    //@ ens Tree(result, 0, nonempty(result, leftShape, rightShape));
    {
        let result = std::alloc::alloc(std::alloc::Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Tree>());
        }
        //@ assume(result as usize & 1 == 0);
        //@ close_struct(result);
        (*result).left = left;
        (*left).parent = result;
        (*result).right = right;
        (*right).parent = result;
        (*result).parent = std::ptr::null_mut();
        result
    }

    unsafe fn new() -> *mut Tree
    //@ req true;
    //@ ens Tree(result, 0, empty(result));
    {
        let result = std::alloc::alloc(std::alloc::Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Tree>());
        }
        //@ assume(result as usize & 1 == 0);
        //@ close_struct(result);
        (*result).left = std::ptr::null_mut();
        (*result).right = std::ptr::null_mut();
        (*result).parent = std::ptr::null_mut();
        result
    }

    unsafe fn visit(root: *mut Tree, visitor: TreeVisitor, visitor_data: *mut u8)
    //@ req Tree(root, 0, ?rootShape) &*& [_]is_TreeVisitor(visitor, ?p) &*& p(visitor_data, node_count(rootShape));
    //@ ens Tree(root, 0, rootShape) &*& p(visitor_data, 0);
    {
        let mut x = root;
        let mut x_is_new = true;
        //@ Tree_inv();
        //@ close stack(0, root, rootShape, root, rootShape, 0, 0);
        //@ close inv_(true, x, root, rootShape, _, _);
        loop {
            //@ inv inv_(x_is_new, x, root, rootShape, ?stepsLeft, ?countTodo) &*& x != 0 &*& [_]is_TreeVisitor(visitor, p) &*& p(visitor_data, countTodo);
            //@ open inv_(_, _, _, _, _, _);
            //@ if x_is_new == false { open stack(x, _, _, _, _, _, _); }
            if x_is_new {
                visitor(visitor_data, x);
            }
            if (*x).left.is_null() {
                x = (*x).parent;
                x_is_new = false;
                //@ close inv_(false, x, root, rootShape, _, _);
            } else {
                if x_is_new {
                    //@ set_lsb((*x).parent as *mut u8);
                    (*x).parent = ((*x).parent as *mut u8).offset(1) as *mut Tree;
                }
                let mut y = (*x).left;
                (*x).left = (*x).right;
                (*x).right = (*x).parent;
                x_is_new = y as usize & 1 == 0;
                if !x_is_new {
                    //@ clear_lsb(y as *mut u8);
                    y = (y as *mut u8).offset(-1) as *mut Tree;
                }
                (*x).parent = y;
                /*@
                if x_is_new {
                    assert Tree(y, x, ?leftShape);
                    close stack(x, y, leftShape, root, rootShape, ?stepsLeft1, _);
                    close inv_(true, y, root, rootShape, _, _);
                } else {
                    close inv_(false, y, root, rootShape, _, _);
                }
                @*/
                x = y;
            }
            if x.is_null() {
                break;
            }
            //@ assert inv_(_, _, _, _, ?stepsLeft1, _) &*& stepsLeft1 < stepsLeft;
        }
        //@ open inv_(_, _, _, _, _, _);
        //@ open stack(_, _, _, _, _, _, _);
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

unsafe fn counting_tree_visitor(data: *mut u8, _node: *mut Tree)
//@ req *(data as *mut i32) |-> ?count &*& count < 0x7fffffff;
//@ ens *(data as *mut i32) |-> count + 1;
{
    *(data as *mut i32) += 1;
}

//@ pred counting_tree_visitor_data(data: *mut u8, countTodo: i32) = *(data as *mut i32) |-> 3 - countTodo;

fn main() {
    unsafe {
        let left_child = Tree::new();
        let right_child = Tree::new();
        let root = Tree::new_with_children(left_child, right_child);

        let count = std::alloc::alloc(std::alloc::Layout::new::<i32>()) as *mut i32;
        if count.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<i32>());
        }
        //@ u8s__to_integer__(count, 4, true);
        *count = 0;

        /*@
        produce_fn_ptr_chunk TreeVisitor(counting_tree_visitor)(counting_tree_visitor_data)(data, node) {
            open counting_tree_visitor_data(data, ?countTodo);
            call();
            close counting_tree_visitor_data(data, countTodo - 1);
        }
        @*/

        //@ close counting_tree_visitor_data(count as *mut u8, 3);
        Tree::visit(root, counting_tree_visitor, count as *mut u8);
        //@ open counting_tree_visitor_data(count as *mut u8, 0);
        assert(*count == 3);
        
        //@ integer__to_u8s(count, 4, true);
        std::alloc::dealloc(count as *mut u8, std::alloc::Layout::new::<i32>());
        
        Tree::dispose(root);
    }
}
