use std::ptr::{self, addr_of_mut};

#[derive(Clone, Copy)]
struct RunClosure {
    run: unsafe fn(*mut u8),
    data: *mut u8
}

// This function is NOT actually safe! It cannot be declared 'unsafe' because libc::pthread_create's signature is broken:
// it wants a safe function pointer.
extern "C" fn run_closure_run(value: *mut libc::c_void) -> *mut libc::c_void {
    unsafe {
        let closure = *(value as *mut RunClosure);
        std::alloc::dealloc(value as *mut u8, std::alloc::Layout::new::<RunClosure>());
        (closure.run)(closure.data);
        ptr::null_mut()
    }
}

pub unsafe fn fork(run: unsafe fn(data: *mut u8), data: *mut u8) {
    let layout = std::alloc::Layout::new::<RunClosure>();
    let run_closure = std::alloc::alloc(layout) as *mut RunClosure;
    if run_closure.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    ptr::write(addr_of_mut!((*run_closure).run), run);
    ptr::write(addr_of_mut!((*run_closure).data), data);
    let mut id = std::mem::MaybeUninit::<libc::pthread_t>::uninit();
    let result = libc::pthread_create(id.as_mut_ptr(), ptr::null(), run_closure_run, run_closure as *mut libc::c_void);
    if result != 0 {
        eprintln!("pthread_create() returned error code {}", result);
        std::process::abort();
    }
    libc::pthread_detach(id.assume_init());
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
