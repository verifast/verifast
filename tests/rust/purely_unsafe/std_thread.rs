use std::thread::JoinHandle;
//@ use std::thread::JoinHandle;

/*@

fn_type FuncOnce<T, U>(pre: pred(T), post: pred(T, U)) = unsafe fn(arg: T) -> U;
    req pre(arg);
    ens post(arg, result);

pred JoinHandle<U>(join_handle: JoinHandle<U>, post: pred(U));

pred_ctor post_<T, U>(post: pred(T, U), arg: T)(result: U) = post(arg, result);

@*/

type FuncOnce<T, U> = unsafe fn(arg: T) -> U;

unsafe fn spawn<T: Send + 'static, U: Send + 'static>(f: FuncOnce<T, U>, arg: T) -> JoinHandle<U>
//@ req [_]is_FuncOnce::<T, U>(f, ?pre, ?post) &*& pre(arg);
//@ ens JoinHandle(result, post_(post, arg));
//@ assume_correct
{
    std::thread::spawn(move || {
        unsafe { f(arg) }
    })
}

unsafe fn join<U>(join_handle: JoinHandle<U>) -> U
//@ req JoinHandle(join_handle, ?post);
//@ ens post(result);
//@ assume_correct
{
    join_handle.join().unwrap()
}

unsafe fn increment(arg: i32) -> i32
//@ req arg < i32::MAX;
//@ ens result == arg + 1;
{
    arg + 1
}

fn main() {
    unsafe {
    {
        /*@
        pred pre(arg: i32) = arg < i32::MAX;
        pred post(arg: i32, res: i32) = res == arg + 1;
        @*/
        /*@
        produce_fn_ptr_chunk FuncOnce<i32, i32>(increment)(pre, post)(arg) {
            open pre(arg);
            let outcome = call();
            assert outcome == returning(?res);
            close post(arg, res);
        }
        @*/
        //@ close pre(42);
        let join_handle = spawn(increment, 42);
        let result = join(join_handle);
        //@ open post_::<i32, i32>(post, 42)(_);
        //@ open post(42, _);
        if result != 43 {
            std::hint::unreachable_unchecked();
        }
    }
    }
}
