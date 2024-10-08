// verifast_options{extern:../unverified/platform}

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

pred_ctor space_inv(x: *std::sync::atomic::AtomicUsize)() = [1/2]std::sync::atomic::AtomicUsize(x, ?value) &*& value == 0 || value == 1;

pred incrementor_pre(x: *mut u8) =
    [_]atomic_space(MaskTop, space_inv(x as *std::sync::atomic::AtomicUsize)) &*&
    [1/2]std::sync::atomic::AtomicUsize(x as *std::sync::atomic::AtomicUsize, 0);

@*/

unsafe fn incrementor(x_: *mut u8)
//@ req incrementor_pre(x_);
//@ ens true;
{
    //@ open incrementor_pre(x_);
    let x = &*(x_ as *mut std::sync::atomic::AtomicUsize);
    {
        /*@
        pred pre() = [_]atomic_space(MaskTop, space_inv(x)) &*& [1/2]std::sync::atomic::AtomicUsize(x, 0);
        pred post(result: usize) = true;
        @*/
        /*@
        produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_fetch_add_ghop(x, 1, pre, post)() {
            open pre();
            open_atomic_space(MaskTop, space_inv(x));
            open space_inv(x)();
            assert std::sync::atomic::is_AtomicUsize_fetch_add_op(?op, _, _, _, _);
            assert std::sync::atomic::AtomicUsize(x, ?value);
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
            leak [_]std::sync::atomic::AtomicUsize(x, _);
        };
        @*/
        //@ close pre();
        x.fetch_add(1, SeqCst);
        //@ open post(_);
    }
}

fn main() {
    unsafe {
        let layout = std::alloc::Layout::new::<std::sync::atomic::AtomicUsize>();
        let x_ = std::alloc::alloc(layout) as *mut std::sync::atomic::AtomicUsize;
        if x_.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ from_u8s_(x_);
        std::ptr::write(x_, std::sync::atomic::AtomicUsize::new(0));
        let x = &*x_;
        //@ produce_fn_ptr_chunk platform::threading::thread_run(incrementor)(incrementor_pre)(data) { call(); }
        //@ close space_inv(x)();
        //@ create_atomic_space(MaskTop, space_inv(x));
        //@ leak atomic_space(MaskTop, space_inv(x));
        //@ close incrementor_pre(x_ as *u8);
        platform::threading::fork(incrementor as unsafe fn(*mut u8), x_ as *mut u8);
        let mut x1 = 0;
        {
            /*@
            pred pre() = [_]atomic_space(MaskTop, space_inv(x));
            pred post(result: usize) = result == 0 || result == 1;
            @*/
            /*@
            produce_lem_ptr_chunk std::sync::atomic::AtomicUsize_load_ghop(x, pre, post)() {
                open pre();
                open_atomic_space(MaskTop, space_inv(x));
                open space_inv(x)();
                assert [_]std::sync::atomic::AtomicUsize(x, ?value);
                assert std::sync::atomic::is_AtomicUsize_load_op(?op, _, _, _);
                op();
                close space_inv(x)();
                close_atomic_space(MaskTop);
                close post(value);
            };
            @*/
            //@ close pre();
            x1 = x.load(SeqCst);
            //@ open post(_);
        }
        assert(x1 == 0 || x1 == 1);
        std::process::exit(0);
    }
}
