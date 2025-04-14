// verifast_options{ignore_unwind_paths ignore_ref_creation}

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

struct Node {
    data: *mut u8,
    left: *mut Node,
    right: *mut Node,
    parent: *mut Node,
}

/*@

inductive tree = empty(node: *mut Node) | nonempty(data: *mut u8, node: *mut Node, left: tree, right: tree);

fix node_count(tree: tree) -> i32 {
    match tree {
        empty(node) => 1,
        nonempty(data, node, left, right) => 1 + node_count(left) + node_count(right)
    }
}

fix tree_elems(tree: tree) -> list< *mut u8 > {
    match tree {
        empty(node) => [],
        nonempty(data, node, left, right) => cons(data, append(tree_elems(left), tree_elems(right)))
    }
}

fix tree_root(tree: tree) -> *mut Node {
    match tree {
        empty(node) => node,
        nonempty(data, node, left, right) => node
    }
}

lem_auto node_count_positive(tree: tree)
    req true;
    ens node_count(tree) >= 1;
{
    match tree {
        empty(node) => {}
        nonempty(data, node, left, right) => {
            node_count_positive(left);
            node_count_positive(right);
        }
    }
}

pred Tree(node: *mut Node; parent: *mut Node, shape: tree) =
    node != 0 &*&
    std::alloc::alloc_block(node as *u8, std::alloc::Layout::new_::<Node>()) &*&
    struct_Node_padding(node) &*&
    node as usize & 1 == 0 &*&
    pointer_within_limits(node as *mut u8 + 1) == true &*&
    (*node).data |-> ?data &*&
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
        shape == nonempty(data, node, leftShape, rightShape)
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

pred stack(parent: *mut Node, current: *mut Node, cShape: tree, root: *mut Node, rootShape: tree, stepsLeft: i32, elems_todo: list< *mut u8 >) =
    current != 0 &*&
    if parent == 0 {
        root == current &*&
        rootShape == cShape &*&
        stepsLeft == 0 &*&
        elems_todo == []
    } else {
        std::alloc::alloc_block(parent as *u8, std::alloc::Layout::new_::<Node>()) &*&
        struct_Node_padding(parent) &*&
        parent as usize & 1 == 0 &*&
        pointer_within_limits(parent as *mut u8 + 1) == true &*&
        (*parent).data |-> ?data &*&
        (*parent).left |-> ?left &*&
        (*parent).right |-> ?right &*&
        (*parent).parent |-> current &*&
        if right as usize & 1 != 0 {
            pointer_within_limits(right as *mut u8 - 1) == true &*&
            Tree(left, parent, ?rightShape) &*& left != 0 &*&
            stack((right as *mut u8 - 1) as *mut Node, parent, nonempty(data, parent, cShape, rightShape), root, rootShape, ?stepsLeft1, ?elems_todo0) &*&
            stepsLeft1 >= 0 &*&
            stepsLeft == node_count(rightShape) * 2 + 1 + stepsLeft1 &*&
            elems_todo == append(tree_elems(rightShape), elems_todo0)
        } else {
            left as usize & 1 != 0 &*&
            pointer_within_limits(left as *mut u8 - 1) == true &*&
            Tree(right, parent, ?leftShape) &*& right != 0 &*&
            stack((left as *mut u8 - 1) as *mut Node, parent, nonempty(data, parent, leftShape, cShape), root, rootShape, ?stepsLeft1, elems_todo) &*&
            stepsLeft1 >= 0 &*& stepsLeft == 1 + stepsLeft1
        }
    };

pred inv_(x_is_new: bool, x: *mut Node, root: *mut Node, rootShape: tree, stepsLeft: i32, elems_todo: list< *mut u8 >) =
    if x_is_new {
        Tree(x, ?parent, ?xShape) &*& stack(parent, x, xShape, root, rootShape, ?stepsLeft1, ?elems_todo0) &*&
        stepsLeft1 >= 0 &*& stepsLeft == node_count(xShape) * 2 - 1 + stepsLeft1 &*&
        elems_todo == append(tree_elems(xShape), elems_todo0)
    } else {
        stack(x, ?child, ?childShape, root, rootShape, stepsLeft, elems_todo) &*& stepsLeft >= 0 &*&
        Tree(child, x, childShape)
    };

@*/

pub trait TreeVisitor {

    fn visit<'a>(&'a mut self, node_data: *mut u8);

}

pub struct Tree {
    root: *mut Node,
}

/*@

pred <Tree>.own(t, tree;) = Tree(tree.root, 0, ?shape);

pred hidden_lifetime_token(k: lifetime_t;) = lifetime_token(k);

@*/

impl Tree {

    pub fn new_empty() -> Tree
    {
        unsafe {
            let result = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
            if result.is_null() {
                std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
            }
            //@ assume(result as usize & 1 == 0);
            //@ close_struct(result);
            (*result).data = std::ptr::null_mut();
            (*result).left = std::ptr::null_mut();
            (*result).right = std::ptr::null_mut();
            (*result).parent = std::ptr::null_mut();
            Tree { root: result }
        }
    }

    pub fn new_nonempty(data: *mut u8, left: Tree, right: Tree) -> Tree
    {
        unsafe {
            let mut left_ = std::mem::ManuallyDrop::new(left);
            let mut right_ = std::mem::ManuallyDrop::new(right);
            let result = std::alloc::alloc(std::alloc::Layout::new::<Node>()) as *mut Node;
            if result.is_null() {
                std::alloc::handle_alloc_error(std::alloc::Layout::new::<Node>());
            }
            //@ assume(result as usize & 1 == 0);
            //@ close_struct(result);
            (*result).data = data;
            (*result).left = left_.root;
            (*left_.root).parent = result;
            (*result).right = right_.root;
            (*right_.root).parent = result;
            (*result).parent = std::ptr::null_mut();
            Tree { root: result }
        }
    }

    pub fn accept<'a, V: TreeVisitor>(&'a mut self, visitor: &'a mut V)
    {
        unsafe {
            //@ open_full_borrow(_q_a/2, 'a, Tree_full_borrow_content(_t, self));
            //@ open Tree_full_borrow_content(_t, self)();
            //@ open Tree_own(_t, ?tree);
            Self::accept0::<V>(self.root, true, visitor);
            //@ close Tree_own(_t, tree);
            //@ close Tree_full_borrow_content(_t, self)();
            //@ close_full_borrow(Tree_full_borrow_content(_t, self));
            //@ leak full_borrow(_, _) &*& full_borrow(_, _);
        }
    }

    unsafe fn accept0<'a, V: TreeVisitor>(mut x: *mut Node, mut x_is_new: bool, visitor: &'a mut V)
    //@ req Tree(?root, 0, ?rootShape) &*& x == root &*& x_is_new &*& thread_token(?t) &*& t == currentThread &*& [?q]lifetime_token(?k) &*& full_borrow(k, <V>.full_borrow_content(t, visitor));
    //@ ens Tree(root, 0, rootShape) &*& thread_token(t) &*& [q]lifetime_token(k) &*& full_borrow(k, <V>.full_borrow_content(t, visitor));
    {
        //@ Tree_inv();
        //@ close stack(0, root, rootShape, root, rootShape, 0, []);
        //@ close inv_(true, x, root, rootShape, _, _);
        loop {
            //@ inv inv_(x_is_new, x, root, rootShape, ?stepsLeft, ?elems_todo) &*& x != 0 &*& thread_token(t) &*& [q]lifetime_token(k) &*& full_borrow(k, <V>.full_borrow_content(t, visitor));
            //@ open inv_(_, _, _, _, _, _);
            //@ if x_is_new == false { open stack(x, _, _, _, _, _, _); }
            if (*x).left.is_null() {
                x = (*x).parent;
                x_is_new = false;
                //@ close inv_(false, x, root, rootShape, _, _);
            } else {
                if x_is_new {
                    //@ let k1 = begin_lifetime();
                    //@ let kk1 = lifetime_intersection(k, k1);
                    //@ reborrow(kk1, k, <V>.full_borrow_content(t, visitor));
                    //@ lifetime_token_inv(k);
                    //@ if q < 1 { close [1 - q]hidden_lifetime_token(k1); }
                    //@ close_lifetime_intersection_token(q, k, k1);
                    {
                        //@ let_lft 'b = kk1;
                        visitor.visit/*@::<V, 'b> @*/((*x).data);
                    }
                    //@ if q < 1 { open [1 - q]hidden_lifetime_token(k1); }
                    //@ open_lifetime_intersection_token(q, k, k1);
                    //@ end_lifetime(k1);
                    //@ lifetime_intersection_symm(k, k1);
                    //@ close_lifetime_intersection_dead_token(k1, k);
                    //@ end_reborrow(kk1, k, <V>.full_borrow_content(t, visitor));
                    
                    //@ set_lsb((*x).parent as *mut u8);
                    (*x).parent = ((*x).parent as *mut u8).offset(1) as *mut Node;
                }
                let mut y = (*x).left;
                (*x).left = (*x).right;
                (*x).right = (*x).parent;
                x_is_new = y as usize & 1 == 0;
                if !x_is_new {
                    //@ clear_lsb(y as *mut u8);
                    y = (y as *mut u8).offset(-1) as *mut Node;
                }
                (*x).parent = y;
                /*@
                if x_is_new {
                    assert Tree(y, x, ?leftShape);
                    assert stack(_, x, nonempty(_, _, _, ?rightShape), root, rootShape, _, ?elems_todo0);
                    append_assoc(tree_elems(leftShape), tree_elems(rightShape), elems_todo0);
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

    unsafe fn dispose_unsafe(tree: *mut Node)
    //@ req Tree(tree, _, _);
    //@ ens true;
    {
        if !(*tree).left.is_null() {
            Self::dispose_unsafe((*tree).left);
            Self::dispose_unsafe((*tree).right);
        }
        //@ open_struct(tree);
        std::alloc::dealloc(tree as *mut u8, std::alloc::Layout::new::<Node>());
    }

}

impl Drop for Tree {

    fn drop<'a>(&'a mut self) {
        unsafe {
            //@ open Tree_full_borrow_content(_t, self)();
            Self::dispose_unsafe(self.root);
        }
    }

}
