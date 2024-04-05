use std::io::Write;

unsafe fn memchr(mut haystack: *const u8, mut size: usize, needle: u8) -> *const u8
//@ req [?f]integers_(haystack, 1, false, size, ?cs) &*& size <= isize::MAX;
//@ ens [f]integers_(haystack, 1, false, size, cs) &*& 0 <= result as usize - haystack as usize &*& result as usize - haystack as usize <= size &*& result == haystack + (result as usize - haystack as usize);
{
    //@ let haystack0 = haystack;
    //@ let size0 = size;
    //@ close [f]integers_(haystack, 1, false, 0, []);
    loop {
        //@ inv [f]integers_(haystack0, 1, false, haystack as usize - haystack0 as usize, ?cs0) &*& [f]integers_(haystack, 1, false, size, ?cs1) &*& append(cs0, cs1) == cs &*& haystack == haystack0 + (haystack as usize - haystack0 as usize);
        if size == 0 || *haystack == needle {
            //@ if size != 0 { close [f]integers_(haystack, 1, false, size, _); }
            //@ integers__join(haystack0);
            return haystack;
        }
        haystack = haystack.offset(1);
        size -= 1;
        //@ close [f]integers_(haystack, 1, false, 0, []);
        //@ close [f]integers_(haystack - 1, 1, false, 1, _);
        //@ integers__join(haystack0);
        //@ append_assoc(cs0, [head(cs1)], tail(cs1));
    }
}

unsafe fn read_line<'a>(socket: platform::sockets::Socket, buffer: &'a mut Vec<u8>)
//@ req [?q]platform::sockets::Socket(socket) &*& *buffer |-> ?buffer0 &*& std::vec::Vec(buffer0, _, _);
//@ ens [q]platform::sockets::Socket(socket) &*& *buffer |-> ?buffer1 &*& std::vec::Vec(buffer1, _, _);
{
    let mut offset = buffer.len();
    loop {
        //@ inv [q]platform::sockets::Socket(socket) &*& *buffer |-> ?buffer1 &*& std::vec::Vec(buffer1, _, ?bs) &*& length(bs) == offset;
        const RECV_BUF_SIZE: usize = 1000;
        buffer.reserve(RECV_BUF_SIZE);
        //@ assert *buffer |-> ?buffer2;
        //@ let buf = std::vec::Vec_separate_buffer(buffer2);
        //@ u8_array_to_integers_(buf);
        //@ u8_array__to_integers__(buf + offset);
        //@ integers___split(buf + offset, 1000);
        let count = socket.receive(buffer.as_mut_ptr().add(offset), RECV_BUF_SIZE);
        //@ integers__join(buf);
        //@ integers___join(buf + offset + count);
        if count == 0 {
            //@ integers__to_u8_array(buf);
            //@ integers___to_u8_array_(buf + offset + count);
            //@ std::vec::Vec_unseparate_buffer(buffer2);
            break;
        }
        buffer.set_len(offset + count);
        //@ assert *buffer |-> ?buffer3;
        //@ integers__split(buf, offset);
        let nl_index = memchr(buffer.as_ptr().offset(offset as isize), count, b'\n') as usize - (buffer.as_ptr() as usize + offset);
        if nl_index == count {
            offset += count;
            //@ integers__join(buf);
            //@ integers__to_u8_array(buf);
            //@ integers___to_u8_array_(buf + offset);
            //@ std::vec::Vec_unseparate_buffer(buffer3);
        } else {
            buffer.set_len(offset + nl_index + 1);
            //@ assert *buffer |-> ?buffer4;
            //@ integers__split(buf + offset, nl_index + 1);
            //@ integers__join(buf);
            //@ integers__to_integers__(buf + offset + nl_index + 1);
            //@ integers___join(buf + offset + nl_index + 1);
            //@ integers__to_u8_array(buf);
            //@ integers___to_u8_array_(buf + offset + nl_index + 1);
            //@ std::vec::Vec_unseparate_buffer(buffer4);
            return;
        }
    }
}

unsafe fn send_bytes<'a>(socket: platform::sockets::Socket, bytes: &'a [u8])
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft]integers_(bytes.ptr, 1, false, bytes.len, _);
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft]integers_(bytes.ptr, 1, false, bytes.len, _);
{
    socket.send(bytes.as_ptr(), bytes.len());
}

unsafe fn send_str<'a>(socket: platform::sockets::Socket, text: &'a str)
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft]integers_(text.ptr, 1, false, text.len, _);
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft]integers_(text.ptr, 1, false, text.len, _);
{
    send_bytes(socket, text.as_bytes());
}

unsafe fn handle_connection<'a>(buffer: &'a mut Vec<u8>, socket: platform::sockets::Socket)
//@ req *buffer |-> ?buffer0 &*& std::vec::Vec(buffer0, _, _) &*& platform::sockets::Socket(socket);
//@ ens *buffer |-> ?buffer1 &*& std::vec::Vec(buffer1, _, _);
{
    read_line(socket, buffer);
    //@ assert *buffer |-> ?buffer1;
    send_str(socket, "HTTP/1.0 200 OK\r\n\r\n");
    let len = buffer.len();
    //@ let buf = std::vec::Vec_separate_buffer(buffer1);
    //@ u8_array_to_integers_(buf);
    socket.send(buffer.as_ptr(), len);
    //@ integers__to_u8_array(buf);
    //@ std::vec::Vec_unseparate_buffer(buffer1);
    socket.close();
}

unsafe fn print<'a>(text: &'a str)
//@ req thread_token(?t) &*& [?f]integers_(text.ptr, 1, false, text.len, ?cs);
//@ ens thread_token(t) &*& [f]integers_(text.ptr, 1, false, text.len, cs);
{
    let mut stdout = std::io::stdout();
    stdout.write(text.as_bytes()).unwrap();
    std::mem::drop(stdout);
}

fn main() {
    unsafe {
        let port: u16 = 10000;
        let server_socket = platform::sockets::Socket::listen(port);
        print("Listening on port 10000...\n");
        let mut buffer = Vec::new();
        loop {
            //@ inv platform::sockets::ServerSocket(server_socket) &*& buffer |-> ?buffer_ &*& std::vec::Vec(buffer_, _, _);
            let client_socket = server_socket.accept();
            handle_connection(&mut buffer, client_socket);
        }
    }
}
