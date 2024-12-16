use std::{mem::ManuallyDrop, ptr};

#[derive(Clone, Copy)]
pub struct Thread {
    id: libc::pthread_t
}

struct RunClosure<Arg> {
    run: unsafe fn(Arg),
    data: Arg
}

// This function is NOT actually safe! It cannot be declared 'unsafe' because libc::pthread_create's signature is broken:
// it wants a safe function pointer.
extern "C" fn run_closure_run<Arg>(value: *mut libc::c_void) -> *mut libc::c_void {
    unsafe {
        let closure = (value as *mut RunClosure<Arg>).read();
        std::alloc::dealloc(value as *mut u8, std::alloc::Layout::new::<RunClosure<Arg>>());
        (closure.run)(closure.data);
        ptr::null_mut()
    }
}

pub unsafe fn fork_joinable<Arg>(run: unsafe fn(data: Arg), data: Arg) -> Thread {
    let layout = std::alloc::Layout::new::<RunClosure<Arg>>();
    let run_closure = std::alloc::alloc(layout) as *mut RunClosure<Arg>;
    if run_closure.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    ptr::write(&raw mut (*run_closure).run, run);
    ptr::write(&raw mut (*run_closure).data, data);
    let mut id = std::mem::MaybeUninit::<libc::pthread_t>::uninit();
    let result = libc::pthread_create(id.as_mut_ptr(), ptr::null(), run_closure_run::<Arg>, run_closure as *mut libc::c_void);
    if result != 0 {
        eprintln!("pthread_create() returned error code {}", result);
        std::process::abort();
    }
    Thread { id: id.assume_init() }
}

pub unsafe fn join(thread: Thread) {
    let thread = ManuallyDrop::new(thread);
    let result = libc::pthread_join(thread.id, ptr::null_mut());
    if result != 0 {
        eprintln!("pthread_join() returned error code {}", result);
        std::process::abort();
    }
}

pub unsafe fn fork<Arg>(run: unsafe fn(data: Arg), data: Arg) {
    let thread = fork_joinable(run, data);
    libc::pthread_detach(thread.id);
}

#[derive(Clone, Copy)]
pub struct Mutex {
    mutex: *mut libc::pthread_mutex_t
}

impl Mutex {

    pub unsafe fn new() -> Mutex {
        let layout = std::alloc::Layout::new::<libc::pthread_mutex_t>();
        let mutex = std::alloc::alloc(layout) as *mut libc::pthread_mutex_t;
        if mutex.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        let mut attributes: std::mem::MaybeUninit<libc::pthread_mutexattr_t> = std::mem::MaybeUninit::uninit();
        {
            let result = libc::pthread_mutexattr_init(attributes.as_mut_ptr());
            if result != 0 {
                eprintln!("pthread_mutexattr_init() returned error code {}", result);
                std::process::abort();
            }
        }
        {
            let result = libc::pthread_mutexattr_settype(attributes.as_mut_ptr(), libc::PTHREAD_MUTEX_ERRORCHECK);
            if result != 0 {
                eprintln!("pthread_mutexattr_settype() returned error code {}", result);
                std::process::abort();
            }
        }
        {
            let result = libc::pthread_mutex_init(mutex, attributes.as_mut_ptr());
            if result != 0 {
                eprintln!("pthread_mutex_init() returned error code {}", result);
                std::process::abort();
            }
        }
        {
            let result = libc::pthread_mutexattr_destroy(attributes.as_mut_ptr());
            if result != 0 {
                eprintln!("pthread_mutexattr_destroy() returned error code {}", result);
                std::process::abort();
            }
        }
        Mutex { mutex }
    }

    pub unsafe fn acquire(self) {
        let result = libc::pthread_mutex_lock(self.mutex);
        if result != 0 {
            eprintln!("pthread_mutex_lock() returned error code {}", result);
            std::process::abort();
        }
    }

    /// Returns `true` if this call successfully acquired the mutex. Returns `false` if the mutex could not be acquired.
    pub unsafe fn try_acquire(self) -> bool {
        let result = libc::pthread_mutex_trylock(self.mutex);
        if result == libc::EBUSY {
            return false
        }
        if result != 0 {
            eprintln!("pthread_mutex_trylock() returned error code {}", result);
            std::process::abort();
        }
        true
    }

    pub unsafe fn release(self) {
        let result = libc::pthread_mutex_unlock(self.mutex);
        if result != 0 {
            eprintln!("pthread_mutex_unlock() returned error code {}", result);
            std::process::abort();
        }
    }

    pub unsafe fn dispose(self) {
        let result = libc::pthread_mutex_destroy(self.mutex);
        if result != 0 {
            eprintln!("pthread_mutex_destroy() returned error code {}", result);
            std::process::abort();
        }
    }

}
