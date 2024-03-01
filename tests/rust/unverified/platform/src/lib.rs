pub mod sockets;

#[cfg(unix)]
#[path = "threading_unix.rs"]
pub mod threading;

#[cfg(all(windows, target_arch = "x86_64"))]
#[path = "threading_windows.rs"]
pub mod threading;
