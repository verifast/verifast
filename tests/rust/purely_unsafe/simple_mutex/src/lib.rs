// verifast_options{extern_spec:platform=../../unverified/platform/spec/lib.rsspec}

pub struct Mutex {
    mutex: platform::threading::Mutex,
}

impl Copy for Mutex {}

impl Clone for Mutex {

    fn clone(&self) -> Mutex {
        //@ assume(false); //~allow_dead_code
        *self //~allow_dead_code
    } //~allow_dead_code

}

/*@

pred_ctor Mutex_inv(mutex: platform::threading::Mutex, held_token: i32, held_frac_cell: i32, inv_: pred())() =
    [1/2]platform::threading::Mutex_state(mutex, ?state) &*&
    match state {
        none() => inv_() &*& [1/2]platform::threading::Mutex_state(mutex, state) &*& ghost_cell::<real>(held_frac_cell, _),
        some(owner) => [1/2]ghost_cell::<real>(held_frac_cell, ?heldFrac) &*& 0 < heldFrac &*& [heldFrac]ghost_cell::<unit>(held_token, unit),
    };

pub pred Mutex(mutex: Mutex, inv_: pred();) =
    platform::threading::Mutex(mutex.mutex, ?ghost_cell_id) &*&
    ghost_cell::<i32>(ghost_cell_id, ?ghost_cell0_id) &*&
    ghost_cell::<pair<i32, i32>>(ghost_cell0_id, pair(?held_token, ?held_frac_cell)) &*&
    ghost_cell::<unit>(held_token, unit) &*&
    atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_));

pub pred Mutex_held(mutex: Mutex, inv_: pred(), owner: usize, frac: real) =
    [frac]platform::threading::Mutex(mutex.mutex, ?ghost_cell_id) &*&
    [frac]ghost_cell::<i32>(ghost_cell_id, ?ghost_cell0_id) &*&
    [frac]ghost_cell::<pair<i32, i32>>(ghost_cell0_id, pair(?held_token, ?held_frac_cell)) &*&
    [1/2]ghost_cell(held_frac_cell, frac) &*&
    [frac]atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)) &*&
    [1/2]platform::threading::Mutex_state(mutex.mutex, some(owner));

@*/

impl Mutex {

    pub unsafe fn new() -> Mutex
    //@ req exists::<pred()>(?inv_) &*& inv_();
    //@ ens Mutex(result, inv_);
    {
        //@ open exists(_);
        let mutex = platform::threading::Mutex::new();
        //@ assert platform::threading::Mutex(mutex, ?ghost_cell_id);
        //@ let held_token = create_ghost_cell::<unit>(unit);
        //@ let held_frac_cell = create_ghost_cell::<real>(0);
        //@ let ghost_cell0_id = create_ghost_cell(pair(held_token, held_frac_cell));
        //@ ghost_cell_mutate(ghost_cell_id, ghost_cell0_id);
        //@ close Mutex_inv(mutex, held_token, held_frac_cell, inv_)();
        //@ create_atomic_space(MaskTop, Mutex_inv(mutex, held_token, held_frac_cell, inv_));
        Mutex { mutex }
    }

    pub unsafe fn acquire(mutex: Mutex)
    //@ req [?f]Mutex(mutex, ?inv_);
    //@ ens Mutex_held(mutex, inv_, currentThread, f) &*& inv_();
    {
        //@ let acquirer = currentThread;
        //@ open Mutex(mutex, inv_);
        //@ assert [f]platform::threading::Mutex(mutex.mutex, ?ghost_cell_id);
        //@ assert [f]ghost_cell::<i32>(ghost_cell_id, ?ghost_cell0_id);
        //@ assert [f]ghost_cell(ghost_cell0_id, pair(?held_token, ?held_frac_cell));
        //@ ghost_cell_fraction_info(held_token);
        {
            /*@
            pred pre() =
                [f]atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)) &*&
                [f]ghost_cell(held_token, unit);
            pred post() =
                [f]atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)) &*&
                [1/2]ghost_cell::<real>(held_frac_cell, f) &*&
                [1/2]platform::threading::Mutex_state(mutex.mutex, some(acquirer)) &*& inv_();
            @*/
            /*@
            produce_lem_ptr_chunk platform::threading::Mutex_acquire_ghop(mutex.mutex, currentThread, pre, post)() {
                assert platform::threading::is_Mutex_acquire_op(?op, _, _, _, _);
                open pre();
                open_atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_));
                open Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)();
                op();
                ghost_cell_mutate(held_frac_cell, f);
                close Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)();
                close_atomic_space(MaskTop);
                close post();
            };
            @*/
            //@ close pre();
            mutex.mutex.acquire();
            //@ open post();
        }
        //@ close Mutex_held(mutex, inv_, currentThread, f);
    }

    pub unsafe fn release(mutex: Mutex)
    //@ req Mutex_held(mutex, ?inv_, currentThread, ?f) &*& inv_();
    //@ ens [f]Mutex(mutex, inv_);
    {
        //@ open Mutex_held(mutex, inv_, currentThread, f);
        //@ assert [f]platform::threading::Mutex(mutex.mutex, ?ghost_cell_id);
        //@ assert [f]ghost_cell::<i32>(ghost_cell_id, ?ghost_cell0_id);
        //@ assert [f]ghost_cell(ghost_cell0_id, pair(?held_token, ?held_frac_cell));
        //@ let releaser = currentThread;
        {
            /*@
            pred pre() =
                [f]atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)) &*&
                [1/2]ghost_cell(held_frac_cell, f) &*&
                [1/2]platform::threading::Mutex_state(mutex.mutex, some(releaser)) &*& inv_();
            pred post() =
                [f]ghost_cell(held_token, unit) &*&
                [f]atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_));
            @*/
            /*@
            produce_lem_ptr_chunk platform::threading::Mutex_release_ghop(mutex.mutex, currentThread, pre, post)() {
                assert platform::threading::is_Mutex_release_op(?op, _, _, _, _);
                open pre();
                open_atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_));
                open Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)();
                op();
                close Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)();
                close_atomic_space(MaskTop);
                close post();
            };
            @*/
            //@ close pre();
            mutex.mutex.release();
            //@ open post();
        }
    }
    
    pub unsafe fn dispose(mutex: Mutex)
    //@ req Mutex(mutex, ?inv_);
    //@ ens inv_();
    {
        //@ open Mutex(mutex, inv_);
        //@ assert platform::threading::Mutex(mutex.mutex, ?ghost_cell_id);
        //@ assert ghost_cell::<i32>(ghost_cell_id, ?ghost_cell0_id);
        //@ assert ghost_cell(ghost_cell0_id, pair(?held_token, ?held_frac_cell));
        //@ destroy_atomic_space(MaskTop, Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_));
        //@ open Mutex_inv(mutex.mutex, held_token, held_frac_cell, inv_)();
        //@ ghost_cell_fraction_info::<unit>(held_token);
        platform::threading::Mutex::dispose(mutex.mutex);
        //@ ghost_cell_leak::<pair<i32, i32>>(ghost_cell0_id);
        //@ ghost_cell_leak::<unit>(held_token);
        //@ ghost_cell_leak::<real>(held_frac_cell);
    }

}
