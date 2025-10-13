// verifast_options{ignore_unwind_paths}
#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{alloc, handle_alloc_error, Layout};

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

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

/// `true` means the sensor has been removed.
unsafe fn wait_for_pulse(_source: i32) -> bool
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_u32(n: u32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", n);
}

//@ pred_ctor Counter(counter: *mut u32)() = *counter |-> ?count;

struct CountPulsesData {
    counter: *mut u32,
    mutex: *mut Mutex,
    source: i32,
}

//@ pred count_pulses_pre(data: CountPulsesData) = [_]Mutex(data.mutex, Counter(data.counter));

unsafe fn count_pulses(data: CountPulsesData)
//@ req count_pulses_pre(data);
//@ ens true;
{
    //@ open count_pulses_pre(data);
    let CountPulsesData {counter, mutex, source} = data;

    loop {
        //@ inv [_]Mutex(mutex, Counter(counter));
        let done = wait_for_pulse(source);
        if done { break }
        let guard = acquire(mutex);
        //@ open Counter(counter)();
        *counter = (*counter).checked_add(1).unwrap();
        //@ close Counter(counter)();
        release(guard);
    }
}

unsafe fn count_pulses_async(counter: *mut u32, mutex: *mut Mutex, source: i32)
//@ req [_]Mutex(mutex, Counter(counter));
//@ ens true;
{
    let data = CountPulsesData { counter, mutex, source };
    //@ close count_pulses_pre(data);
    //@ produce_fn_ptr_chunk Spawnee<CountPulsesData>(count_pulses)(count_pulses_pre)(data_) { call(); }
    spawn(count_pulses, data);
}

struct PrintCountData {
    counter: *mut u32,
    mutex: *mut Mutex,
}

//@ pred print_count_pre(data: PrintCountData) = [_]Mutex(data.mutex, Counter(data.counter));

unsafe fn print_count(data: PrintCountData)
//@ req print_count_pre(data);
//@ ens true;
{
    //@ open print_count_pre(data);
    let PrintCountData {counter, mutex} = data;
    loop {
        //@ inv [_]Mutex(mutex, Counter(counter));
        std::thread::sleep(std::time::Duration::from_millis(1000));
        let guard = acquire(mutex);
        //@ open Counter(counter)();
        print_u32(*counter);
        //@ close Counter(counter)();
        release(guard);
    }
}

unsafe fn print_count_async(counter: *mut u32, mutex: *mut Mutex)
//@ req [_]Mutex(mutex, Counter(counter));
//@ ens true;
{
    let data = PrintCountData { counter, mutex };
    //@ close print_count_pre(data);
    //@ produce_fn_ptr_chunk Spawnee<PrintCountData>(print_count)(print_count_pre)(data_) { call(); }
    spawn(print_count, data);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let counter = alloc(Layout::new::<u32>()) as *mut u32;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<u32>());
        }
        *counter = 0;
        //@ close Counter(counter)();
        //@ close exists(Counter(counter));
        let mutex = create_mutex();
        //@ leak Mutex(mutex, _);

        print_count_async(counter, mutex);

        loop {
            //@ inv [_]Mutex(mutex, Counter(counter));
            let source = wait_for_source();
            count_pulses_async(counter, mutex, source);
        }
    }
}
