//@ use std::alloc::{Layout, alloc_block};

struct Node {
    next: *mut Node,
    value: i32,
}

/*@

pred Nodes(node: *mut Node, count: i32) =
    if node == 0 {
        count == 0
    } else {
        0 < count &*&
        (*node).next |-> ?next &*&
        (*node).value |-> ?value &*&
        struct_Node_padding(node) &*&
        alloc_block(node as *mut u8, Layout::new::<Node>()) &*&
        Nodes(next, count - 1)
    };

pred lseg(first: *mut Node, last: *mut Node, count: i32) =
    if first == last {
        count == 0
    } else {
        0 < count &*& first != 0 &*&
        (*first).value |-> ?value &*& (*first).next |-> ?next &*&
        struct_Node_padding(first) &*&
        alloc_block(first as *mut u8, Layout::new::<Node>()) &*&
        lseg(next, last, count - 1)
    };

lem Nodes_to_lseg_lemma(first: *mut Node)
    req Nodes(first, ?count);
    ens lseg(first, 0, count);
{
    open Nodes(first, count);
    if first != 0 {
        Nodes_to_lseg_lemma((*first).next);
    }
    close lseg(first, 0, count);
}

lem lseg_to_Nodes_lemma(first: *mut Node)
    req lseg(first, 0, ?count);
    ens Nodes(first, count);
{
    open lseg(first, 0, count);
    if first != 0 {
        lseg_to_Nodes_lemma((*first).next);
    }
    close Nodes(first, count);
}

@*/
