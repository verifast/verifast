unsafe fn print_socket_error_message(api: &std::ffi::CStr) {
    libc::perror(api.as_ptr());
}

const INVALID_SOCKET: libc::c_int = -1;

#[derive(Copy, Clone)]
pub struct Socket {
    socket: libc::c_int
}

impl Socket {
    pub unsafe fn listen(port: u16) -> Socket {
        let server_socket = libc::socket(libc::PF_INET, libc::SOCK_STREAM, libc::IPPROTO_TCP);
        if INVALID_SOCKET == server_socket {
            print_socket_error_message(c"socket()");
            std::process::abort();
        }
        let mut server_name: libc::sockaddr_in = std::mem::zeroed();
        server_name.sin_addr.s_addr = u32::to_be(libc::INADDR_ANY);
        server_name.sin_family = libc::AF_INET.try_into().unwrap();
        server_name.sin_port = u16::to_be(port);
    
        {
            let status = libc::bind(server_socket, &server_name as *const libc::sockaddr_in as *const libc::sockaddr, std::mem::size_of::<libc::sockaddr_in>().try_into().unwrap());
            if INVALID_SOCKET == status {
                print_socket_error_message(c"bind()");
                std::process::abort();
            }
        }
    
        {
            let status = libc::listen(server_socket, 5); // Allow 5 pending incoming connection requests
            if INVALID_SOCKET == status {
                print_socket_error_message(c"listen()");
                std::process::abort();
            }
        }
    
        return Socket { socket: server_socket };
    }
    
    pub unsafe fn accept(self) -> Socket {
        let mut client_name: libc::sockaddr_in = std::mem::zeroed();
        let mut client_name_length: libc::socklen_t = std::mem::size_of::<libc::sockaddr_in>().try_into().unwrap();
        let client_socket = libc::accept(self.socket, &mut client_name as *mut libc::sockaddr_in as *mut libc::sockaddr, &mut client_name_length as *mut libc::socklen_t);
        if INVALID_SOCKET == client_socket {
            print_socket_error_message(c"accept()");
            std::process::abort();
        }
    
        return Socket { socket: client_socket };
    }

    pub unsafe fn receive(self, buffer: *mut u8, length: usize) -> usize {
        let result = libc::recv(self.socket, buffer as *mut libc::c_void, length, 0);
        if result < 0 {
            print_socket_error_message(c"recv()");
            std::process::abort();
        }
        result.try_into().unwrap()
    }

    pub unsafe fn send(self, buffer: *const u8, length: usize) {
        if libc::send(self.socket, buffer as *mut libc::c_void, length, 0) < 0 {
            // print_socket_error_message(c"send");
            // std::process::abort();
        }
    }

    pub unsafe fn close(self) {
        libc::close(self.socket);
    }
    
}
