struct Node {
    next: *mut Node,
}

/*@

pred Nodes(n: *mut Node; nodes: list<*mut Node>) =
    if n == 0 {
        nodes == nil
    } else {
        (*n).next |-> ?next &*& Nodes(next, ?nodes0) &*& nodes == cons(n, nodes0)
    };

@*/

impl Node {

    unsafe fn reverse(mut n: *mut Node) -> *mut Node
    //@ req Nodes(n, ?nodes);
    //@ ens Nodes(result, reverse(nodes));
    //@ on_unwind_ens false;
    {
        let mut m = std::ptr::null_mut();
        loop {
            //@ inv Nodes(n, ?n_nodes) &*& Nodes(m, ?m_nodes) &*& reverse(nodes) == append(reverse(n_nodes), m_nodes);
            //@ open Nodes(n, _);
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            //@ append_assoc(reverse(tail(n_nodes)), [n], m_nodes);
            (*n).next = m;
            m = n;
            n = k;
        }
    }

}

fn main() {
    unsafe {
        let mut node1 = Node { next: std::ptr::null_mut() };
        let mut node2 = Node { next: &raw mut node1 };
        let result = Node::reverse(&raw mut node2);
        //@ open Nodes(_, _);
        //@ open Nodes(_, _);
        //@ open Nodes(_, _);
        std::hint::assert_unchecked(result == &raw mut node1);
        std::hint::assert_unchecked(node1.next == &raw mut node2);
        std::hint::assert_unchecked(node2.next.is_null());
    }
}
