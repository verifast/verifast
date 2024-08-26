use std::io::Write;

unsafe fn memchr(mut haystack: *const u8, mut size: usize, needle: u8) -> *const u8
//@ req [?f]haystack[..size] |-> ?cs &*& size <= isize::MAX;
//@ ens [f]haystack[..size] |-> cs &*& 0 <= result as usize - haystack as usize &*& result as usize - haystack as usize <= size &*& result == haystack + (result as usize - haystack as usize);
{
    loop {
        /*@
        req [f]haystack[..size] |-> ?cs1;
        ens
            [f]old_haystack[..old_size] |-> cs1 &*&
            haystack == old_haystack + (haystack as usize - old_haystack as usize) &*&
            0 <= haystack as usize - old_haystack as usize &*&
            haystack as usize - old_haystack as usize <= old_size;
        @*/
        //@ open array(haystack, _, _);
        if size == 0 || *haystack == needle {
            return haystack;
        }
        haystack = haystack.offset(1);
        size -= 1;
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
        //@ array__split(buf + offset, 1000);
        let count = socket.receive(buffer.as_mut_ptr().add(offset), RECV_BUF_SIZE);
        //@ array_join(buf);
        //@ array__join(buf + offset + count);
        if count == 0 {
            //@ std::vec::Vec_unseparate_buffer(buffer2);
            break;
        }
        buffer.set_len(offset + count);
        //@ assert *buffer |-> ?buffer3;
        //@ array_split(buf, offset);
        let nl_index = memchr(buffer.as_ptr().offset(offset as isize), count, b'\n') as usize - (buffer.as_ptr() as usize + offset);
        if nl_index == count {
            offset += count;
            //@ array_join(buf);
            //@ std::vec::Vec_unseparate_buffer(buffer3);
        } else {
            buffer.set_len(offset + nl_index + 1);
            //@ assert *buffer |-> ?buffer4;
            //@ array_split(buf + offset, nl_index + 1);
            //@ array_join(buf);
            //@ array_to_array_(buf + offset + nl_index + 1);
            //@ array__join(buf + offset + nl_index + 1);
            //@ std::vec::Vec_unseparate_buffer(buffer4);
            return;
        }
    }
}

unsafe fn send_bytes<'a>(socket: platform::sockets::Socket, bytes: &'a [u8])
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft]bytes.ptr[..bytes.len] |-> ?bs;
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft]bytes.ptr[..bytes.len] |-> bs;
{
    socket.send(bytes.as_ptr(), bytes.len());
}

unsafe fn send_str<'a>(socket: platform::sockets::Socket, text: &'a str)
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft]text.ptr[..text.len] |-> ?bs;
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft]text.ptr[..text.len] |-> bs;
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
    socket.send(buffer.as_ptr(), len);
    //@ std::vec::Vec_unseparate_buffer(buffer1);
    socket.close();
}

unsafe fn print<'a>(text: &'a str)
//@ req thread_token(?t) &*& [?f]text.ptr[..text.len] |-> ?cs;
//@ ens thread_token(t) &*& [f]text.ptr[..text.len] |-> cs;
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
