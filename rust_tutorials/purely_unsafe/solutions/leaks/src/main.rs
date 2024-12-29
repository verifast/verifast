// verifast_options{disable_overflow_check extern_spec:platform=../../../../tests/rust/unverified/platform/spec/lib.rsspec extern_spec:simple_mutex=../../../../tests/rust/purely_unsafe/simple_mutex/spec/lib.rsspec}

use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};
use simple_mutex::Mutex;
//@ use std::alloc::{Layout, alloc_block};
//@ use simple_mutex::Mutex;

unsafe fn wait_for_source() -> i32
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    42
}

unsafe fn wait_for_pulse(_source: i32) -> bool // true means the sensor has been removed.
//@ req true;
//@ ens true;
{
    std::thread::sleep(std::time::Duration::from_millis(500));
    false
}

unsafe fn print_i32(n: i32)
//@ req true;
//@ ens true;
//@ assume_correct
{
    println!("{}", n);
}

struct Counter {
    count: i32,
    mutex: Mutex,
}

//@ pred_ctor Counter(counter: *mut Counter)() = (*counter).count |-> ?count;

struct CountPulsesData {
    counter: *mut Counter,
    source: i32,
}

/*@

pred count_pulses_pre(data: *mut CountPulsesData) =
    (*data).counter |-> ?counter &*&
    (*data).source |-> ?source &*&
    struct_CountPulsesData_padding(data) &*&
    alloc_block(data as *u8, Layout::new_::<CountPulsesData>()) &*&
    [_](*counter).mutex |-> ?mutex &*& [_]Mutex(mutex, Counter(counter));

@*/

unsafe fn count_pulses(data: *mut CountPulsesData)
//@ req count_pulses_pre(data);
//@ ens true;
{
    //@ open count_pulses_pre(data);
    let counter = (*data).counter;
    let source = (*data).source;
    //@ open_struct(data);
    dealloc(data as *mut u8, Layout::new::<CountPulsesData>());

    let mutex = (*counter).mutex;

    loop {
        //@ inv [_]Mutex(mutex, Counter(counter));
        let done = wait_for_pulse(source);
        if done { break }
        Mutex::acquire(mutex);
        //@ open Counter(counter)();
        (*counter).count += 1;
        //@ close Counter(counter)();
        Mutex::release(mutex);
    }
}

unsafe fn count_pulses_async(counter: *mut Counter, source: i32)
//@ req [_](*counter).mutex |-> ?mutex &*& [_]Mutex(mutex, Counter(counter));
//@ ens true;
{
    let data = alloc(Layout::new::<CountPulsesData>()) as *mut CountPulsesData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<CountPulsesData>());
    }
    //@ close_struct(data);
    (*data).counter = counter;
    (*data).source = source;
    //@ close count_pulses_pre(data);
    //@ produce_fn_ptr_chunk platform::threading::thread_run<*CountPulsesData>(count_pulses)(count_pulses_pre)(data_) { call(); }
    platform::threading::fork(count_pulses, data);
}

/*@

pred print_count_pre(counter: *mut Counter) =
    [_](*counter).mutex |-> ?mutex &*& [_]Mutex(mutex, Counter(counter));

@*/

unsafe fn print_count(counter: *mut Counter)
//@ req print_count_pre(counter);
//@ ens true;
{
    //@ open print_count_pre(counter);
    let mutex = (*counter).mutex;
    loop {
        //@ inv [_]Mutex(mutex, Counter(counter));
        std::thread::sleep(std::time::Duration::from_millis(1000));
        Mutex::acquire(mutex);
        //@ open Counter(counter)();
        print_i32((*counter).count);
        //@ close Counter(counter)();
        Mutex::release(mutex);
    }
}

fn main() {
    unsafe {
        let counter = alloc(Layout::new::<Counter>()) as *mut Counter;
        if counter.is_null() {
            handle_alloc_error(Layout::new::<Counter>());
        }
        //@ close_struct(counter);
        (*counter).count = 0;
        //@ close Counter(counter)();
        //@ close exists(Counter(counter));
        let mutex = Mutex::new();
        (*counter).mutex = mutex;
        //@ leak (*counter).mutex |-> mutex &*& Mutex(mutex, _);

        //@ close print_count_pre(counter);
        //@ produce_fn_ptr_chunk platform::threading::thread_run<*mut Counter>(print_count)(print_count_pre)(counter_) { call(); }
        platform::threading::fork(print_count, counter);

        loop {
            //@ inv [_](*counter).mutex |-> mutex &*& [_]Mutex(mutex, Counter(counter));
            let source = wait_for_source();
            count_pulses_async(counter, source);
        }
    }
}
