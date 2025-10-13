// verifast_options{ignore_unwind_paths}
use std::alloc::{Layout, alloc, handle_alloc_error};

/*@

fn_type Spawnee<T>(pre: pred(T)) = unsafe fn(arg: T);
    req pre(arg);
    ens true;

@*/

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

unsafe fn spawn<T: 'static>(f: unsafe fn(arg: T), arg: T)
//@ req [_]is_Spawnee(f, ?pre) &*& pre(arg);
//@ ens true;
//@ assume_correct
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        f(package_moved.payload)
    });
}

type Mutex = std::sync::Mutex<()>;
type MutexGuard = std::sync::MutexGuard<'static, ()>;

//@ pred Mutex(mutex: *mut Mutex; inv_: pred());
//@ pred MutexGuard(guard: MutexGuard, mutex: *mut Mutex, inv_: pred(), frac: real, t: thread_id_t);

unsafe fn create_mutex() -> *mut Mutex
//@ req exists::<pred()>(?inv_) &*& inv_();
//@ ens Mutex(result, inv_);
//@ assume_correct
{
    let mutex = alloc(Layout::new::<Mutex>()) as *mut Mutex;
    if mutex.is_null() { handle_alloc_error(Layout::new::<Mutex>()); }
    mutex.write(Mutex::new(()));
    mutex
}

unsafe fn acquire(mutex: *mut Mutex) -> MutexGuard
//@ req [?frac]Mutex(mutex, ?inv_);
//@ ens MutexGuard(result, mutex, inv_, frac, currentThread) &*& inv_();
//@ assume_correct
{
    (*mutex).lock().unwrap()
}

unsafe fn release(guard: MutexGuard)
//@ req MutexGuard(guard, ?mutex, ?inv_, ?frac, currentThread) &*& inv_();
//@ ens [frac]Mutex(mutex, inv_);
//@ assume_correct
{
    drop(guard);
}

unsafe fn wait_for_pulse(_source: i32)
//@ req true;
//@ ens true;
{
    // For simplicity, instead of actually waiting for input
    // from a sensor, we just sleep for 500ms.
    std::thread::sleep(std::time::Duration::from_millis(500)); 
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", n);
}

//@ pred_ctor counter_inv(counter: *mut u32)() = *counter |-> ?count;

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ pred count_pulses_pre(data: CountPulsesData) = [1/3]Mutex(data.mutex, counter_inv(data.counter));

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_pre(data);
//@ ens true;
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ inv [1/3]Mutex(mutex, counter_inv(counter));
        wait_for_pulse(source);
        let guard = acquire(mutex);
        //@ open counter_inv(counter)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close counter_inv(counter)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [1/3]Mutex(mutex, counter_inv(counter));
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_pre(data);
    //@ produce_fn_ptr_chunk Spawnee<CountPulsesData>(count_pulses)(count_pulses_pre)(arg) { call(); }
    spawn(count_pulses, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() { handle_alloc_error(Layout::new::<u32>()); }
        *counter = 0;
        //@ close counter_inv(counter)();
        //@ close exists(counter_inv(counter));
        let mutex = create_mutex();

        count_pulses_async(counter, mutex, 1);
        count_pulses_async(counter, mutex, 2);

        loop {
            //@ inv [1/3]Mutex(mutex, counter_inv(counter));
            std::thread::sleep(std::time::Duration::from_millis(1000));
            let guard = acquire(mutex);
            //@ open counter_inv(counter)();
            let count = *counter;
            //@ close counter_inv(counter)();
            release(guard);
            print_u32(count);
        }
    }
}
