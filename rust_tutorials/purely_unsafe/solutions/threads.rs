// verifast_options{ignore_unwind_paths extern:../../../tests/rust/unverified/platform disable_overflow_check}

use std::alloc::{Layout, alloc, handle_alloc_error};
//use platform::threading::Thread;
//@ use std::alloc::{Layout, alloc_block};
//@ use platform::threading::{Thread, thread_run_joinable};

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
            let value = random_int(5);
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

struct SumData {
    thread: platform::threading::Thread,
    tree: *mut Tree,
    sum: i32,
}

/*@

pred_ctor summator_post(data: *SumData)() =
    (*data).tree |-> ?tree &*& Tree(tree, _) &*& (*data).sum |-> ?sum;
pred summator_pre(data: *SumData, post: pred()) =
    (*data).tree |-> ?tree &*& Tree(tree, _) &*& (*data).sum |-> _ &*&
    post == summator_post(data);

@*/

unsafe fn summator(data: *mut SumData)
//@ req summator_pre(data, ?post);
//@ ens post();
{
    //@ open summator_pre(data, _);
    let sum = Tree::compute_sum_facs((*data).tree);
    (*data).sum = sum;
    //@ close summator_post(data)();
}

unsafe fn start_sum_thread(tree: *mut Tree) -> *mut SumData
//@ req Tree(tree, _);
//@ ens (*result).thread |-> ?t &*& Thread(t, summator_post(result));
{
    let data = alloc(Layout::new::<SumData>()) as *mut SumData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<SumData>());
    }
    //@ leak alloc_block_SumData(data);
    (*data).tree = tree;
    //@ close summator_pre(data, summator_post(data));
    /*@
    produce_fn_ptr_chunk thread_run_joinable<*SumData>(summator)(summator_pre)(data_) {
        call();
    }
    @*/
    let t = platform::threading::fork_joinable(summator, data);
    (*data).thread = t;
    data
}

unsafe fn join_sum_thread(data: *mut SumData) -> i32
//@ req (*data).thread |-> ?t &*& Thread(t, summator_post(data));
//@ ens true;
{
    platform::threading::join((*data).thread);
    //@ open summator_post(data)();
    let result = (*data).sum;
    //@ leak (*data).tree |-> ?tree &*& Tree(tree, _) &*& (*data).sum |-> _ &*& (*data).thread |-> _;
    result
}

unsafe fn print_i32(value: i32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        //@ open Tree(tree, _);
        let left_data = start_sum_thread((*tree).left);
        let right_data = start_sum_thread((*tree).right);
        let sum_left = join_sum_thread(left_data);
        let sum_right = join_sum_thread(right_data);
        let f = fac((*tree).value);
        //@ leak (*tree).left |-> _ &*& (*tree).right |-> _ &*& (*tree).value |-> _ &*& alloc_block_Tree(tree);
        print_i32(sum_left + sum_right + f);
    }
}
