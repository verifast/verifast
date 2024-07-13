use std::{ptr::null_mut, sync::atomic::{AtomicUsize, Ordering::SeqCst}};

unsafe fn assert(b: bool)
//@ req b;
//@ ens true;
{
    if !b { //~allow_dead_code
        *null_mut() = 42; //~allow_dead_code
    }
}

/*@

pred_ctor space_inv(x: *mut usize)() = [1/2](*x |-> ?value) &*& value == 0 || value == 1;

pred incrementor_pre(x: *mut u8) = [_]atomic_space(MaskTop, space_inv(x as *usize)) &*& [1/2](*(x as *usize) |-> 0);

@*/

unsafe fn incrementor(x_: *mut u8)
//@ req incrementor_pre(x_);
//@ ens true;
{
    let x = x_ as *mut usize;
    //@ open incrementor_pre(x_);
    {
        /*@
        pred pre() = [_]atomic_space(MaskTop, space_inv(x)) &*& [1/2](*x |-> 0);
        pred post(result: usize) = true;
        @*/
        /*@
        produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_fetch_add_ghop(x as *std::sync::atomic::AtomicUsize, 1, pre, post)() {
            open pre();
            open_atomic_space(MaskTop, space_inv(x));
            open space_inv(x)();
            assert std::sync::atomic::is_AtomicUsize_fetch_add_op(?op, _, _, _, _);
            assert *x |-> ?value &*& value == 0;
            div_rem_nonneg(value + 1, usize::MAX + 1);
            if (value + 1) / (usize::MAX + 1) > 0 {
            } else {
                if (value + 1) / (usize::MAX + 1) < 0 {
                } else {
                }
            }
            op();
            close space_inv(x)();
            close_atomic_space(MaskTop);
            close post(0);
            leak [_](*x |-> _);
        };
        @*/
        //@ close pre();
        AtomicUsize::from_ptr(x as *mut usize).fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        //@ open post(_);
    }
}

fn main() {
    unsafe {
        let layout = std::alloc::Layout::from_size_align_unchecked(std::mem::size_of::<usize>(), std::mem::size_of::<usize>());
        let x = std::alloc::alloc(layout) as *mut usize;
        if x.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ u8s__to_integer__(x, std::mem::size_of::<usize>(), false);
        std::ptr::write(x, 0);
        //@ produce_fn_ptr_chunk platform::threading::thread_run(incrementor)(incrementor_pre)(data) { call(); }
        //@ close space_inv(x)();
        //@ create_atomic_space(MaskTop, space_inv(x));
        //@ leak atomic_space(MaskTop, space_inv(x));
        //@ close incrementor_pre(x as *u8);
        platform::threading::fork(incrementor as unsafe fn(*mut u8), x as *mut u8);
        let mut x1 = 0;
        {
            /*@
            pred pre() = [_]atomic_space(MaskTop, space_inv(x));
            pred post(result: usize) = result == 0 || result == 1;
            @*/
            /*@
            produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_load_ghop(x as *std::sync::atomic::AtomicUsize, pre, post)() {
                open pre();
                open_atomic_space(MaskTop, space_inv(x));
                open space_inv(x)();
                assert [_](*x |-> ?value);
                assert std::sync::atomic::is_AtomicUsize_load_op(?op, _, _, _);
                op();
                close space_inv(x)();
                close_atomic_space(MaskTop);
                close post(value);
            };
            @*/
            //@ close pre();
            x1 = AtomicUsize::from_ptr(x).load(SeqCst);
            //@ open post(_);
        }
        assert(x1 == 0 || x1 == 1);
        std::process::exit(0);
    }
}
