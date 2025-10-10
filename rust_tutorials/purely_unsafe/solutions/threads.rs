// verifast_options{ignore_unwind_paths}
#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};
//@ use std::alloc::{Layout, alloc_block};
//@ use std::thread::JoinHandle;

/*@

fn_type Spawnee<A, R>(pre: pred(A, pred(R))) = unsafe fn(arg: A) -> R;
    req pre(arg, ?post);
    ens post(result);

pred JoinHandle<R>(h: JoinHandle<Sendable<R>>, post: pred(R));

@*/

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
//@ req [_]is_Spawnee::<A, R>(f, ?pre) &*& pre(arg, ?post);
//@ ens JoinHandle(result, post);
//@ assume_correct
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
//@ req JoinHandle(h, ?post);
//@ ens post(result);
//@ assume_correct
{
    h.join().unwrap().payload
}

unsafe fn wrapping_fib(n: u16) -> u64
//@ req true;
//@ ens true;
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv k <= n;
            
            if k == n { break; }
            
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

/*@

pred Tree(t: *mut Tree, depth: u8) =
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

    unsafe fn make(depth: u8) -> *mut Tree
    //@ req true;
    //@ ens Tree(result, depth);
    {
        if depth == 0 {
            //@ close Tree(0, 0);
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000; // TODO: Use a random number here
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

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req Tree(tree, ?depth);
    //@ ens Tree(tree, depth);
    {
        if tree.is_null() {
            0
        } else {
            //@ open Tree(tree, depth);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close Tree(tree, depth);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

}

unsafe fn print_u64(value: u64)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", value);
}

/*@
pred_ctor compute_sum_fibs_post(tree: *mut Tree, depth: i32)(result: u64) = Tree(tree, depth);
pred compute_sum_fibs_pre(tree: *mut Tree, post: pred(u64)) =
    Tree(tree, ?depth) &*& post == compute_sum_fibs_post(tree, depth);
@*/

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = Tree::make(22);
        //@ open Tree(tree, 22);
        let left = (*tree).left;
        let right = (*tree).right;
        /*@
        produce_fn_ptr_chunk Spawnee<*mut Tree, u64>(Tree::compute_sum_fibs)(compute_sum_fibs_pre)(arg) {
            open compute_sum_fibs_pre(arg, _);
            assert Tree(arg, ?depth);
            let result = call();
            close compute_sum_fibs_post(arg, depth)(result);
        }
        @*/
        //@ close compute_sum_fibs_pre(left, _);
        let left_join_handle = spawn(Tree::compute_sum_fibs, left);
        //@ close compute_sum_fibs_pre(right, _);
        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);
        //@ open compute_sum_fibs_post(left, 21)(_);
        let right_sum = join(right_join_handle);
        //@ open compute_sum_fibs_post(right, 21)(_);
        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);
        
        //@ close Tree(tree, 22);
        //@ leak Tree(tree, 22);
        print_u64(sum)
    }
}
