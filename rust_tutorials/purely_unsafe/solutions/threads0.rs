// verifast_options{ignore_unwind_paths disable_overflow_check}

use std::alloc::{Layout, alloc, handle_alloc_error};
//@ use std::alloc::{Layout, alloc_block};

unsafe fn random_int(max: i32) -> i32
//@ req 0 < max;
//@ ens 0 <= result && result < max;
{
    max - 1 // TODO: Replace by an actual random number generator
}

unsafe fn fac(mut x: i32) -> i32
//@ req true;
//@ ens true;
{
    let mut result = 1;
    loop {
        //@ inv true;
        if x == 1 {
            return result;
        }
        result *= x;
        x -= 1;
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: i32,
}

/*@

pred Tree(t: *mut Tree, depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        (*t).left |-> ?left &*& Tree(left, depth - 1) &*&
        (*t).right |-> ?right &*& Tree(right, depth - 1) &*&
        (*t).value |-> ?value &*&
        alloc_block_Tree(t)
    };

@*/

impl Tree {

    unsafe fn make(depth: i32) -> *mut Tree
    //@ req true;
    //@ ens Tree(result, depth);
    {
        if depth == 0 {
            //@ close Tree(0, 0);
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = random_int(2000);
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close Tree(t, depth);
            t
        }
    }

    unsafe fn compute_sum_facs(tree: *mut Tree) -> i32
    //@ req Tree(tree, ?depth);
    //@ ens Tree(tree, depth);
    {
        if tree.is_null() {
            1
        } else {
            //@ open Tree(tree, depth);
            let left_sum = Self::compute_sum_facs((*tree).left);
            let right_sum = Self::compute_sum_facs((*tree).right);
            let f = fac((*tree).value);
            //@ close Tree(tree, depth);
            left_sum + right_sum + f
        }
    }

}

fn print_i32(value: i32) {}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_facs(tree);
        //@ leak Tree(tree, _);
        print_i32(sum)
    }
}
