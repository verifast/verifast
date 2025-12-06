struct Node {
    next: *mut Node,
}

/*@

pred Nodes(n: *mut Node) =
    if n == 0 {
        true
    } else {
        (*n).next |-> ?next &*& Nodes(next)
    };

@*/

impl Node {

    unsafe fn reverse(mut n: *mut Node) -> *mut Node
    //@ req Nodes(n);
    //@ ens Nodes(result);
    //@ on_unwind_ens false;
    {
        let mut m = std::ptr::null_mut();
        //@ close Nodes(0);
        loop {
            //@ inv Nodes(n) &*& Nodes(m);
            //@ open Nodes(n);
            if n.is_null() {
                return m;
            }
            let k = (*n).next;
            (*n).next = m;
            m = n;
            n = k;
            //@ close Nodes(m);
        }
    }

}

fn main() {
    unsafe {
        //@ close Nodes(0);
        let mut node1 = Node { next: std::ptr::null_mut() };
        //@ close Nodes(&node1);
        let mut node2 = Node { next: &raw mut node1 };
        //@ close Nodes(&node2);
        Node::reverse(&raw mut node2);
        std::process::abort();
    }
}
