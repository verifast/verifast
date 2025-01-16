// verifast_options{ignore_unwind_paths}

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{}

/*@

pred list(n: **u8; nodes: list< **u8 >) =
    if n == 0 {
        nodes == nil
    } else {
        std::alloc::alloc_block(n as *u8, std::alloc::Layout::new_::< * u8>()) &*&
        *n |-> ?next &*& list(next as **u8, ?nodes1) &*& nodes == cons(n, nodes1)
    };

@*/

unsafe fn dispose_list(mut n: *mut *mut u8)
//@ req list(n, _);
//@ ens true;
{
    loop {
        //@ inv list(n, _);
        //@ open list(n, _);
        if n.is_null() {
            break;
        } else {
            let next = *n as *mut *mut u8;
            //@ to_u8s_(n);
            std::alloc::dealloc(n as *mut u8, std::alloc::Layout::new::<*mut u8>());
            n = next;
        }
    }
}        

unsafe fn reverseAppend(list1: *mut *mut u8, list2: *mut *mut u8) -> *mut *mut u8
//@ req list(list1, ?nodes1) &*& list(list2, ?nodes2);
//@ ens list(result, append(reverse(nodes1), nodes2));
{
    //@ open list(list1, nodes1);
    if list1.is_null() {
        return list2;
    } else {
        let next = *list1 as *mut *mut u8;
        *list1 = list2 as *mut u8;
        //@ close list(list1, cons(list1, nodes2));
        //@ append_assoc(reverse(tail(nodes1)), [list1], nodes2);
        return reverseAppend(next, list1);
    }
}

unsafe fn reverse_(n: *mut *mut u8) -> *mut *mut u8
//@ req list(n, ?nodes);
//@ ens list(result, reverse(nodes));
{
    return reverseAppend(n, std::ptr::null_mut());
}

fn main() {
    unsafe {
        let layout = std::alloc::Layout::new::<*mut u8>();
        let node1 = std::alloc::alloc(layout) as *mut *mut u8;
        if node1.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(node1);
        let node2 = std::alloc::alloc(layout) as *mut *mut u8;
        if node2.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(node2);
        let node3 = std::alloc::alloc(layout) as *mut *mut u8;
        if node3.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(node3);
        *node3 = std::ptr::null_mut();
        //@ close list(node3, [node3]);
        *node2 = node3 as *mut u8;
        //@ close list(node2, [node2, node3]);
        *node1 = node2 as *mut u8;
        //@ close list(node1, [node1, node2, node3]);
        let newNode1 = reverse_(node1);
        //@ open list(newNode1, [node3, node2, node1]);
        let newNode2 = *newNode1 as *mut *mut u8;
        //@ open list(newNode2, [node2, node1]);
        let newNode3 = *newNode2 as *mut *mut u8;
        //@ open list(newNode3, [node1]);
        //@ open list(_, []);
        assert(newNode1 == node3);
        assert(newNode2 == node2);
        assert(newNode3 == node1);
        //@ to_u8s_(node1);
        std::alloc::dealloc(node1 as *mut u8, layout);
        //@ to_u8s_(node2);
        std::alloc::dealloc(node2 as *mut u8, layout);
        //@ to_u8s_(node3);
        std::alloc::dealloc(node3 as *mut u8, layout);
    }
}
