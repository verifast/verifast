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

pred Tree(t: *mut Tree; depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        (*t).left |-> ?left &*& Tree(left, ?childDepth) &*&
        (*t).right |-> ?right &*& Tree(right, childDepth) &*&
        (*t).value |-> ?value &*&
        struct_Tree_padding(t) &*&
        alloc_block(t as *u8, Layout::new_::<Tree>()) &*&
        depth == childDepth + 1
    };

fn_type FoldFunction() = unsafe fn(acc: i32, x: i32) -> i32;
    req true;
    ens true;

@*/

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {

    unsafe fn make(depth: i32) -> *mut Tree
    //@ req true;
    //@ ens Tree(result, depth);
    {
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = random_int(5);
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ close_struct(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            t
        }
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree, _);
    //@ ens true;
    {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            //@ open_struct(tree);
            std::alloc::dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req [?frac]Tree(tree, ?depth) &*& [_]is_FoldFunction(f);
    //@ ens [frac]Tree(tree, depth);
    {
        if tree.is_null() {
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            acc
        }
    }

}

struct FoldData {
    thread: platform::threading::Thread,
    tree: *mut Tree,
    f: FoldFunction,
    acc: i32,
}

/*@

pred_ctor folder_post(data: *FoldData)() =
    [1/2](*data).tree |-> ?tree &*& [1/2]Tree(tree, _) &*&
    (*data).f |-> ?f &*& [_]is_FoldFunction(f) &*&
    (*data).acc |-> ?acc;
pred folder_pre(data: *FoldData, post: pred()) =
    [1/2](*data).tree |-> ?tree &*& [1/2]Tree(tree, _) &*&
    (*data).f |-> ?f &*& [_]is_FoldFunction(f) &*&
    (*data).acc |-> ?acc &*&
    post == folder_post(data);

@*/

unsafe fn folder(data: *mut FoldData)
//@ req folder_pre(data, ?post);
//@ ens post();
{
    //@ open folder_pre(data, _);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close folder_post(data)();
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req [1/2]Tree(tree, _) &*& [_]is_FoldFunction(f);
//@ ens [1/2](*result).tree |-> tree &*& (*result).thread |-> ?t &*& Thread(t, folder_post(result)) &*& struct_FoldData_padding(result) &*& alloc_block(result as *u8, Layout::new_::<FoldData>());
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    //@ close_struct(data);
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    //@ close folder_pre(data, folder_post(data));
    /*@
    produce_fn_ptr_chunk thread_run_joinable<*FoldData>(folder)(folder_pre)(data_) {
        call();
    }
    @*/
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req [1/2](*data).tree |-> ?tree &*& (*data).thread |-> ?t &*& Thread(t, folder_post(data)) &*& struct_FoldData_padding(data) &*& alloc_block(data as *u8, Layout::new_::<FoldData>());
//@ ens [1/2]Tree(tree, _);
{
    platform::threading::join((*data).thread);
    //@ open folder_post(data)();
    let result = (*data).acc;
    //@ open_struct(data);
    std::alloc::dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

unsafe fn sum_function(acc: i32, x: i32) -> i32
//@ req true;
//@ ens true;
{
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32
//@ req true;
//@ ens true;
{
    acc ^ fac(x)
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
        let tree = Tree::make(21);
        //@ produce_fn_ptr_chunk FoldFunction(sum_function)()(acc, x) { call(); }
        let sum_data = start_fold_thread(tree, sum_function, 0);
        //@ produce_fn_ptr_chunk FoldFunction(xor_function)()(acc, x) { call(); }
        let xor_data = start_fold_thread(tree, xor_function, 0);
        let sum = join_fold_thread(sum_data);
        let xor = join_fold_thread(xor_data);
        Tree::dispose(tree);
        print_i32(sum - xor);
    }
}
