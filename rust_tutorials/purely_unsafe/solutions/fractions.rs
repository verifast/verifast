// verifast_options{ignore_unwind_paths}
#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};
//@ use std::{alloc::Layout, thread::JoinHandle};

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
    //@ req [?frac]Tree(tree, ?depth);
    //@ ens [frac]Tree(tree, depth);
    {
        if tree.is_null() {
            0
        } else {
            //@ open [frac]Tree(tree, depth);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close [frac]Tree(tree, depth);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
    
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req [?frac]Tree(tree, ?depth);
    //@ ens [frac]Tree(tree, depth);
    {
        if tree.is_null() {
            1
        } else {
            //@ open [frac]Tree(tree, depth);
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close [frac]Tree(tree, depth);
            left_product.wrapping_mul(f).wrapping_mul(right_product)
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
pred_ctor inspect_tree_post(tree: *mut Tree, depth: i32)(result: u64) =
    [1/2]Tree(tree, depth);
pred inspect_tree_pre(tree: *mut Tree, post: pred(u64)) =
    [1/2]Tree(tree, ?depth) &*& post == inspect_tree_post(tree, depth);
@*/

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = Tree::make(22);
        
        /*@
        produce_fn_ptr_chunk Spawnee<*mut Tree, u64>(Tree::compute_sum_fibs)
            (inspect_tree_pre)(arg) {
            open inspect_tree_pre(arg, _);
            assert [1/2]Tree(arg, ?depth);
            let result = call();
            close inspect_tree_post(arg, depth)(result);
        }
        @*/
        //@ close inspect_tree_pre(tree, _);
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        /*@
        produce_fn_ptr_chunk Spawnee<*mut Tree, u64>(Tree::compute_product_fibs)
            (inspect_tree_pre)(arg) {
            open inspect_tree_pre(arg, _);
            assert [1/2]Tree(arg, ?depth);
            let result = call();
            close inspect_tree_post(arg, depth)(result);
        }
        @*/
        //@ close inspect_tree_pre(tree, _);
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        //@ open inspect_tree_post(tree, 22)(_);
        //@ leak [1/2]Tree(tree, 22);
        
        let product = join(product_join_handle);
        //@ open inspect_tree_post(tree, 22)(_);
        //@ leak [1/2]Tree(tree, 22);
        
        print_u64(sum);
        print_u64(product);
    }
}
