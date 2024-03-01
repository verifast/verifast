use std::ptr::{self, addr_of_mut};

#[allow(non_camel_case_types)]
mod c {
    pub type WIN32_ERROR = u32;

    pub type LPTHREAD_START_ROUTINE = ::core::option::Option<
        unsafe extern "system" fn(lpthreadparameter: *mut ::core::ffi::c_void) -> u32,
    >;
    pub type THREAD_CREATION_FLAGS = u32;
    pub type HANDLE = *mut ::core::ffi::c_void;

    #[repr(C)]
    pub struct CRITICAL_SECTION { data: [u64; 5] } // sizeof=40; alignof=8 on x86_64
    type BOOL = libc::c_int;

    #[link(name = "kernel32")]
    extern "system" {
        pub fn GetLastError() -> WIN32_ERROR;
        pub fn CreateThread(
            lpthreadattributes: *const u8,
            dwstacksize: usize,
            lpstartaddress: LPTHREAD_START_ROUTINE,
            lpparameter: *const ::core::ffi::c_void,
            dwcreationflags: THREAD_CREATION_FLAGS,
            lpthreadid: *mut u32,
        ) -> HANDLE;
        pub fn CloseHandle(hobject: HANDLE) -> BOOL;

        // pub fn GetCurrentThreadId() -> u32;

        pub fn InitializeCriticalSection(critical_section: *mut CRITICAL_SECTION);
        pub fn EnterCriticalSection(critical_section: *mut CRITICAL_SECTION);
        pub fn TryEnterCriticalSection(critical_section: *mut CRITICAL_SECTION) -> BOOL;
        pub fn LeaveCriticalSection(critical_section: *mut CRITICAL_SECTION);
        pub fn DeleteCriticalSection(critical_section: *mut CRITICAL_SECTION);
    }
}

#[derive(Clone, Copy)]
struct RunClosure {
    run: unsafe fn(*mut u8),
    data: *mut u8
}

unsafe extern "system" fn run_closure_run(value: *mut libc::c_void) -> u32 {
    unsafe {
        let closure = *(value as *mut RunClosure);
        std::alloc::dealloc(value as *mut u8, std::alloc::Layout::new::<RunClosure>());
        (closure.run)(closure.data);
        0
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
    let handle = c::CreateThread(ptr::null_mut(), 0, Some(run_closure_run), data as *mut libc::c_void, 0, ptr::null_mut());
    if handle == ptr::null_mut() {
        eprintln!("CreateThread() failed; GetLastError() == {}", c::GetLastError());
        std::process::abort();
    }
    {
        let result = c::CloseHandle(handle);
        if result == 0 {
            eprintln!("CloseHandle() failed; GetLastError() == {}", c::GetLastError());
            std::process::abort();
        }
    }
}

struct MutexState {
    critical_section: c::CRITICAL_SECTION,
    owned: bool,
}

#[derive(Clone, Copy)]
pub struct Mutex {
    state: *mut MutexState
}

impl Mutex {

    pub unsafe fn new() -> Mutex {
        let layout = std::alloc::Layout::new::<MutexState>();
        let state = std::alloc::alloc(layout) as *mut MutexState;
        if state.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        (*state).owned = false;
        c::InitializeCriticalSection(addr_of_mut!((*state).critical_section));
        Mutex { state }
    }

    pub unsafe fn acquire(self) {
        c::EnterCriticalSection(addr_of_mut!((*self.state).critical_section));
        if (*self.state).owned {
            eprintln!("The current thread re-entered the mutex");
            std::process::abort();
        }
        (*self.state).owned = true;
    }

    /// Returns `true` if this call successfully acquired the mutex. Returns `false` if the mutex could not be acquired.
    pub unsafe fn try_acquire(self) -> bool {
        let result = c::TryEnterCriticalSection(addr_of_mut!((*self.state).critical_section));
        if result != 0 {
            if (*self.state).owned {
                eprintln!("The current thread re-entered the mutex");
                std::process::abort();
            }
            (*self.state).owned = true;
        }
        result != 0
    }

    pub unsafe fn release(self) {
        (*self.state).owned = false;
        c::LeaveCriticalSection(addr_of_mut!((*self.state).critical_section));
    }

    pub unsafe fn dispose(self) {
        c::DeleteCriticalSection(addr_of_mut!((*self.state).critical_section));
        std::alloc::dealloc(self.state as *mut u8, std::alloc::Layout::new::<MutexState>());
    }

}