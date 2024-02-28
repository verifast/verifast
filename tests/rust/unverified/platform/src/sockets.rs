#[cfg(windows)]
mod c {
    pub type CHAR = libc::c_char;

    #[repr(C)]
    #[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
    pub struct WSADATA {
        pub wVersion: u16,
        pub wHighVersion: u16,
        pub iMaxSockets: u16,
        pub iMaxUdpDg: u16,
        pub lpVendorInfo: PSTR,
        pub szDescription: [u8; 257],
        pub szSystemStatus: [u8; 129],
    }

    pub type WSA_ERROR = i32;

    pub type ADDRESS_FAMILY = u16;
    pub const AF_INET: ADDRESS_FAMILY = 2u16;
    pub const PF_INET: ADDRESS_FAMILY = AF_INET;
    pub const SOCK_STREAM: i32 = 1;
    pub const IPPROTO_TCP: i32 = 6;

    pub type SOCKET = usize;
    pub const INVALID_SOCKET: SOCKET = -1i32 as _;

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct in_addr {
        pub s_addr: u32,
    }

    pub const INADDR_ANY: u32 = 0;

    #[repr(C)]
    pub struct sockaddr {
        pub sa_family: ADDRESS_FAMILY,
        pub sa_data: [u8; 14],
    }

    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct sockaddr_in {
        pub sin_family: ADDRESS_FAMILY,
        pub sin_port: u16,
        pub sin_addr: in_addr,
        pub sin_zero: [CHAR; 8],
    }

    pub type socklen_t = c_int;

    pub type SEND_RECV_FLAGS = i32;

    #[link(name = "ws2_32")] 
    extern "system" { 
        pub fn WSAStartup(wversionrequested: u16, lpwsadata: *mut WSADATA) -> i32; 
        pub fn WSAGetLastError() -> WSA_ERROR;
        pub fn socket(af: i32, type_: i32, protocol: i32) -> SOCKET;
        pub fn bind(s: SOCKET, name: *const sockaddr, namelen: i32) -> i32;
        pub fn listen(s: SOCKET, backlog: i32) -> i32;
        pub fn accept(s: SOCKET, addr: *mut sockaddr, addrlen: *mut i32) -> SOCKET;
        pub fn recv(s: SOCKET, buf: PSTR, len: i32, flags: SEND_RECV_FLAGS) -> i32;
        pub fn send(s: SOCKET, buf: PCSTR, len: i32, flags: SEND_RECV_FLAGS) -> i32;
        pub fn closesocket(s: SOCKET) -> i32;
    }
}

#[cfg(unix)]
use libc as c;

#[cfg(windows)]
unsafe fn print_socket_error_message(api: &std::ffi::CStr) {
    println!("Socket API call '{}' failed: error code {}\n", api, c::WSAGetLastError());
}

#[cfg(unix)]
unsafe fn print_socket_error_message(api: &std::ffi::CStr) {
    libc::perror(api.as_ptr());
}

#[cfg(windows)]
type SOCKET = c::SOCKET;

#[cfg(windows)]
const INVALID_SOCKET: SOCKET = c::INVALID_SOCKET;

#[cfg(unix)]
type SOCKET = libc::c_int;

#[cfg(unix)]
const INVALID_SOCKET: SOCKET = -1;

#[derive(Copy, Clone)]
pub struct Socket {
    socket: SOCKET
}

impl Socket {

    #[cfg(windows)]
    unsafe fn initialize_sockets_api() {
        let windowsSocketsApiData: libc::WSADATA;
        libc::WSAStartup(libc::MAKEWORD(2, 0), &mut windowsSocketsApiData);
    }

    #[cfg(unix)]
    unsafe fn initialize_sockets_api() {}

    pub unsafe fn listen(port: u16) -> Socket {

        Self::initialize_sockets_api();

        let server_socket: SOCKET = c::socket(c::PF_INET, c::SOCK_STREAM, c::IPPROTO_TCP);
        if INVALID_SOCKET == server_socket {
            print_socket_error_message(c"socket()");
            std::process::abort();
        }
        let mut server_name: c::sockaddr_in = std::mem::zeroed();
        server_name.sin_addr.s_addr = u32::to_be(c::INADDR_ANY);
        server_name.sin_family = c::AF_INET.try_into().unwrap();
        server_name.sin_port = u16::to_be(port);
    
        {
            let status = c::bind(server_socket, &server_name as *const c::sockaddr_in as *const c::sockaddr, std::mem::size_of::<c::sockaddr_in>().try_into().unwrap());
            if INVALID_SOCKET == status {
                print_socket_error_message(c"bind()");
                std::process::abort();
            }
        }
    
        {
            let status = c::listen(server_socket, 5); // Allow 5 pending incoming connection requests
            if INVALID_SOCKET == status {
                print_socket_error_message(c"listen()");
                std::process::abort();
            }
        }
    
        return Socket { socket: server_socket };
    }
    
    pub unsafe fn accept(self) -> Socket {
        let mut client_name: c::sockaddr_in = std::mem::zeroed();
        let mut client_name_length: c::socklen_t = std::mem::size_of::<c::sockaddr_in>().try_into().unwrap();
        let client_socket = c::accept(self.socket, &mut client_name as *mut c::sockaddr_in as *mut c::sockaddr, &mut client_name_length as *mut c::socklen_t);
        if INVALID_SOCKET == client_socket {
            print_socket_error_message(c"accept()");
            std::process::abort();
        }
    
        return Socket { socket: client_socket };
    }

    pub unsafe fn receive(self, buffer: *mut u8, length: usize) -> usize {
        let result = c::recv(self.socket, buffer as *mut libc::c_void, length, 0);
        if result < 0 {
            print_socket_error_message(c"recv()");
            std::process::abort();
        }
        result.try_into().unwrap()
    }

    pub unsafe fn send(self, buffer: *const u8, length: usize) {
        if c::send(self.socket, buffer as *mut libc::c_void, length, 0) < 0 {
            // print_socket_error_message(c"send");
            // std::process::abort();
        }
    }

    #[cfg(windows)]
    pub unsafe fn close(self) {
        c::closesocket(self.socket);
    }

    #[cfg(unix)]
    pub unsafe fn close(self) {
        libc::close(self.socket);
    }
    
}
