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
    data: *mut u8,
    left: *mut Tree,
    right: *mut Tree,
    parent: *mut Tree,
}

/*@

inductive tree = empty(node: *mut Tree) | nonempty(data: *mut u8, node: *mut Tree, left: tree, right: tree);

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

fix tree_root(tree: tree) -> *mut Tree {
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

pred Tree(node: *mut Tree; parent: *mut Tree, shape: tree) =
    node != 0 &*&
    std::alloc::alloc_block(node as *u8, std::alloc::Layout::new_::<Tree>()) &*&
    struct_Tree_padding(node) &*&
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

pred stack(parent: *mut Tree, current: *mut Tree, cShape: tree, root: *mut Tree, rootShape: tree, stepsLeft: i32, elems_todo: list< *mut u8 >) =
    current != 0 &*&
    if parent == 0 {
        root == current &*&
        rootShape == cShape &*&
        stepsLeft == 0 &*&
        elems_todo == []
    } else {
        std::alloc::alloc_block(parent as *u8, std::alloc::Layout::new_::<Tree>()) &*&
        struct_Tree_padding(parent) &*&
        parent as usize & 1 == 0 &*&
        pointer_within_limits(parent as *mut u8 + 1) == true &*&
        (*parent).data |-> ?data &*&
        (*parent).left |-> ?left &*&
        (*parent).right |-> ?right &*&
        (*parent).parent |-> current &*&
        if right as usize & 1 != 0 {
            pointer_within_limits(right as *mut u8 - 1) == true &*&
            Tree(left, parent, ?rightShape) &*& left != 0 &*&
            stack((right as *mut u8 - 1) as *mut Tree, parent, nonempty(data, parent, cShape, rightShape), root, rootShape, ?stepsLeft1, ?elems_todo0) &*&
            stepsLeft1 >= 0 &*&
            stepsLeft == node_count(rightShape) * 2 + 1 + stepsLeft1 &*&
            elems_todo == append(tree_elems(rightShape), elems_todo0)
        } else {
            left as usize & 1 != 0 &*&
            pointer_within_limits(left as *mut u8 - 1) == true &*&
            Tree(right, parent, ?leftShape) &*& right != 0 &*&
            stack((left as *mut u8 - 1) as *mut Tree, parent, nonempty(data, parent, leftShape, cShape), root, rootShape, ?stepsLeft1, elems_todo) &*&
            stepsLeft1 >= 0 &*& stepsLeft == 1 + stepsLeft1
        }
    };

pred inv_(x_is_new: bool, x: *mut Tree, root: *mut Tree, rootShape: tree, stepsLeft: i32, elems_todo: list< *mut u8 >) =
    if x_is_new {
        Tree(x, ?parent, ?xShape) &*& stack(parent, x, xShape, root, rootShape, ?stepsLeft1, ?elems_todo0) &*&
        stepsLeft1 >= 0 &*& stepsLeft == node_count(xShape) * 2 - 1 + stepsLeft1 &*&
        elems_todo == append(tree_elems(xShape), elems_todo0)
    } else {
        stack(x, ?child, ?childShape, root, rootShape, stepsLeft, elems_todo) &*& stepsLeft >= 0 &*&
        Tree(child, x, childShape)
    };

pred_fam TreeVisitor(idx: *std::type_info)(visitor_data: *mut u8, elems_todo: list< *mut u8 >, info: any);

@*/

trait TreeVisitor {

    unsafe fn visit(visitor_data: *mut u8, node_data: *mut u8);
    //@ req TreeVisitor(typeid(Self))(visitor_data, cons(node_data, ?elems), ?info);
    //@ ens TreeVisitor(typeid(Self))(visitor_data, elems, info);

}

impl Tree {

    unsafe fn new_nonempty(data: *mut u8, left: *mut Tree, right: *mut Tree) -> *mut Tree
    //@ req Tree(left, _, ?leftShape) &*& Tree(right, _, ?rightShape);
    //@ ens Tree(result, 0, nonempty(data, result, leftShape, rightShape));
    {
        let result = std::alloc::alloc(std::alloc::Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Tree>());
        }
        //@ assume(result as usize & 1 == 0);
        //@ close_struct(result);
        (*result).data = data;
        (*result).left = left;
        (*left).parent = result;
        (*result).right = right;
        (*right).parent = result;
        (*result).parent = std::ptr::null_mut();
        result
    }

    unsafe fn new_empty() -> *mut Tree
    //@ req true;
    //@ ens Tree(result, 0, empty(result));
    {
        let result = std::alloc::alloc(std::alloc::Layout::new::<Tree>()) as *mut Tree;
        if result.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<Tree>());
        }
        //@ assume(result as usize & 1 == 0);
        //@ close_struct(result);
        (*result).data = std::ptr::null_mut();
        (*result).left = std::ptr::null_mut();
        (*result).right = std::ptr::null_mut();
        (*result).parent = std::ptr::null_mut();
        result
    }

    unsafe fn visit<V: TreeVisitor>(root: *mut Tree, visitor_data: *mut u8)
    //@ req Tree(root, 0, ?rootShape) &*& TreeVisitor(typeid(V))(visitor_data, tree_elems(rootShape), ?info);
    //@ ens Tree(root, 0, rootShape) &*& TreeVisitor(typeid(V))(visitor_data, [], info);
    {
        let mut x = root;
        let mut x_is_new = true;
        //@ Tree_inv();
        //@ close stack(0, root, rootShape, root, rootShape, 0, []);
        //@ close inv_(true, x, root, rootShape, _, _);
        loop {
            //@ inv inv_(x_is_new, x, root, rootShape, ?stepsLeft, ?elems_todo) &*& x != 0 &*& TreeVisitor(typeid(V))(visitor_data, elems_todo, info);
            //@ open inv_(_, _, _, _, _, _);
            //@ if x_is_new == false { open stack(x, _, _, _, _, _, _); }
            if (*x).left.is_null() {
                x = (*x).parent;
                x_is_new = false;
                //@ close inv_(false, x, root, rootShape, _, _);
            } else {
                if x_is_new {
                    V::visit(visitor_data, (*x).data);
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

struct CountingTreeVisitor;

/*@

inductive wrap<t> = wrap(t);

pred_fam_inst TreeVisitor(typeid(CountingTreeVisitor))(visitor_data: *mut u8, elems_todo: list< *mut u8 >, maxCount: wrap<i32>) =
    maxCount == wrap(?m) &*& m <= 0x7fffffff &*&
    *(visitor_data as *mut i32) |-> m - length(elems_todo);

@*/

impl TreeVisitor for CountingTreeVisitor {

    unsafe fn visit(visitor_data: *mut u8, _node_data: *mut u8)
    //@ req TreeVisitor(typeid(CountingTreeVisitor))(visitor_data, cons(_node_data, ?elems_todo), ?info);
    //@ ens TreeVisitor(typeid(CountingTreeVisitor))(visitor_data, elems_todo, info);
    {
        //@ open TreeVisitor(typeid(CountingTreeVisitor))(visitor_data, _, wrap(?maxCount));
        let count = *(visitor_data as *mut i32);
        //@ produce_limits(count);
        *(visitor_data as *mut i32) = count + 1;
        //@ close TreeVisitor(typeid(CountingTreeVisitor))(visitor_data, elems_todo, wrap(maxCount));
    }

}

fn main() {
    unsafe {
        let empty1 = Tree::new_empty();
        let empty2 = Tree::new_empty();
        let nonempty1 = Tree::new_nonempty(1 as *mut u8, empty1, empty2);
        let empty3 = Tree::new_empty();
        let empty4 = Tree::new_empty();
        let nonempty2 = Tree::new_nonempty(2 as *mut u8, empty3, empty4);
        let root = Tree::new_nonempty(3 as *mut u8, nonempty1, nonempty2);

        let count = std::alloc::alloc(std::alloc::Layout::new::<i32>()) as *mut i32;
        if count.is_null() {
            std::alloc::handle_alloc_error(std::alloc::Layout::new::<i32>());
        }
        //@ from_u8s_(count);
        *count = 0;

        //@ close TreeVisitor(typeid(CountingTreeVisitor))(count as *mut u8, [3 as *u8, 1 as *u8, 2 as *u8], wrap(3));
        Tree::visit::<CountingTreeVisitor>(root, count as *mut u8);
        //@ open TreeVisitor(typeid(CountingTreeVisitor))(count as *mut u8, [], wrap(3));
        assert(*count == 3);
        
        //@ to_u8s_(count);
        std::alloc::dealloc(count as *mut u8, std::alloc::Layout::new::<i32>());
        
        Tree::dispose(root);
    }
}
