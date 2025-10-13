// verifast_options{ignore_unwind_paths ignore_ref_creation extern:../unverified/platform}

use std::io::Write;
//@ use std::alloc::{alloc_block, Layout};

struct Buffer {
    buffer: *mut u8,
    size: usize,
    length: usize,
}

/*@

pred Buffer_(buffer: Buffer; size: usize, length: usize) =
    size == buffer.size &*& size <= isize::MAX &*&
    length == buffer.length &*&
    alloc_block(buffer.buffer, Layout::from_size_align(size, 1)) &*&
    buffer.buffer[..length] |-> ?_ &*&
    buffer.buffer[length..size] |-> _;

lem_auto Buffer__inv()
    req Buffer_(?buffer, ?size, ?length);
    ens Buffer_(buffer, size, length) &*& size == buffer.size &*& length == buffer.length;
{
    open Buffer_(buffer, size, length);
    close Buffer_(buffer, size, length);
}

pred Buffer(buffer: *Buffer; size: usize, length: usize) =
    struct_Buffer_padding(buffer) &*&
    (*buffer).buffer |-> ?buf &*&
    (*buffer).size |-> size &*&
    (*buffer).length |-> length &*&
    Buffer_(Buffer { buffer: buf, size, length }, size, length);

@*/

impl Buffer {
    unsafe fn new(size: usize) -> Buffer
    //@ req 1 <= size &*& size < isize::MAX;
    //@ ens Buffer_(result, size, 0);
    {
        let layout = std::alloc::Layout::from_size_align_unchecked(size, 1);
        let buffer = std::alloc::alloc(layout);
        if buffer.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ close Buffer_(Buffer { buffer, size, length: 0}, _, _);
        Buffer { buffer, size, length: 0 }
    }

    unsafe fn reserve(buffer: *mut Buffer, mut size: usize)
    //@ req Buffer(buffer, ?size0, ?length) &*& size < isize::MAX;
    //@ ens Buffer(buffer, ?size1, length) &*& size1 - length >= size;
    {
        //@ open Buffer(_, _, _);
        //@ open Buffer_(_, _, _);
        //@ array__inv::<u8>();
        //@ let buf = (*buffer).buffer;
        if (*buffer).size - (*buffer).length < size {
            if size < (*buffer).size {
                size = (*buffer).size; // Always grow by at least a factor of two to avoid too much copying.
            }
            //@ assert size <= isize::MAX;
            if isize::MAX - (size as isize) < (*buffer).size as isize {
                std::process::abort();
            }
            let new_size = (*buffer).size + size;
            let layout = std::alloc::Layout::from_size_align_unchecked((*buffer).size, 1);
            let new_buffer = std::alloc::realloc((*buffer).buffer, layout, new_size);
            if new_buffer.is_null() {
                std::process::abort();
            }
            (*buffer).buffer = new_buffer;
            (*buffer).size = new_size;
            //@ array__join(new_buffer + length);
            //@ close Buffer_(Buffer { buffer: new_buffer, size: new_size, length }, _, _);
        }
    }
}

unsafe fn memchr(mut haystack: *const u8, mut size: usize, needle: u8) -> *const u8
//@ req [?f]haystack[..size] |-> ?cs &*& size <= isize::MAX;
/*@
ens
    [f]haystack[..size] |-> cs &*&
    0 <= result as usize - haystack as usize &*&
    result as usize - haystack as usize <= size &*&
    result == haystack + (result as usize - haystack as usize);
@*/
{
    //@ let haystack0 = haystack;
    //@ let size0 = size;
    loop {
        /*@
        req [f]haystack[..size] |-> ?cs1;
        ens
            [f]old_haystack[..old_size] |-> cs1 &*&
            haystack == old_haystack + (haystack as usize - old_haystack as usize) &*&
            0 <= haystack as usize - old_haystack as usize &*&
            haystack as usize - old_haystack as usize <= old_size;
        @*/
        //@ open array::<u8>(haystack, _, _);
        let done = size == 0 || *haystack == needle;
        //@ if done && size != 0 { close [f]array(haystack, size, _); }
        if done { break }
        haystack = haystack.offset(1);
        size -= 1;
    }
    haystack
}

unsafe fn read_line(socket: platform::sockets::Socket, buffer: *mut Buffer)
//@ req [?q]platform::sockets::Socket(socket) &*& Buffer(buffer, _, _);
//@ ens [q]platform::sockets::Socket(socket) &*& Buffer(buffer, _, _);
{
    let mut offset = (*buffer).length;
    loop {
        //@ inv [q]platform::sockets::Socket(socket) &*& Buffer(buffer, _, offset);
        const RECV_BUF_SIZE: usize = 1000;
        Buffer::reserve(buffer, RECV_BUF_SIZE);
        //@ open Buffer(_, _, _);
        //@ open Buffer_(?buf, _, _);
        //@ array__split(buf.buffer + buf.length, 1000);
        let count = socket.receive((*buffer).buffer.offset((*buffer).length as isize), RECV_BUF_SIZE);
        //@ array_join(buf.buffer);
        //@ array__join(buf.buffer + buf.length + count);
        if count == 0 {
            //@ close Buffer_(buf, _, _);
            break;
        }
        (*buffer).length = offset + count;
        //@ array_split(buf.buffer, offset);
        let nl_index = memchr((*buffer).buffer.offset(offset as isize), count, b'\n') as usize - ((*buffer).buffer as usize + offset);
        if nl_index == count {
            offset += count;
            //@ array_join(buf.buffer);
        } else {
            (*buffer).length = offset + nl_index + 1;
            //@ array_split(buf.buffer + offset, nl_index + 1);
            //@ array_join(buf.buffer);
            //@ array_to_array_(buf.buffer + offset + nl_index + 1);
            //@ array__join(buf.buffer + offset + nl_index + 1);
            return;
        }
    }
}

unsafe fn send_bytes<'a>(socket: platform::sockets::Socket, bytes: &'a [u8])
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft]bytes.ptr[..bytes.len] |-> ?cs;
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft]bytes.ptr[..bytes.len] |-> cs;
{
    socket.send(bytes.as_ptr(), bytes.len());
}

unsafe fn send_str<'a>(socket: platform::sockets::Socket, text: &'a str)
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft]text.ptr[..text.len] |-> ?cs;
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft]text.ptr[..text.len] |-> cs;
{
    send_bytes(socket, text.as_bytes());
}

unsafe fn handle_connection(buffer: *mut Buffer, socket: platform::sockets::Socket)
//@ req Buffer(buffer, _, _) &*& platform::sockets::Socket(socket);
//@ ens Buffer(buffer, _, _);
{
    read_line(socket, buffer);
    send_str(socket, "HTTP/1.0 200 OK\r\n\r\n");
    //@ open Buffer(_, _, _);
    //@ open Buffer_(_, _, _);
    socket.send((*buffer).buffer, (*buffer).length);
    socket.close();
}

unsafe fn print<'a>(text: &'a str)
//@ req thread_token(?t) &*& [?f]text.ptr[..text.len] |-> ?cs;
//@ ens thread_token(t) &*& [f]text.ptr[..text.len] |-> cs;
{
    let mut stdout = std::io::stdout();
    let result = stdout.write(text.as_bytes());
    //@ open std::result::Result_own::<usize, std::io::Error>(t, result);
    result.unwrap();
    std::mem::drop(stdout);
}

fn main() {
    unsafe {
        let port: u16 = 10000;
        let server_socket = platform::sockets::Socket::listen(port);
        print("Listening on port 10000...\n");
        let mut buffer = Buffer::new(1000);
        //@ assert Buffer_(?buf, 1000, 0);
        //@ assert buffer.buffer |-> buf.buffer &*& buffer.size |-> 1000 &*& buffer.length |-> 0;
        //@ assert buf == Buffer { buffer: buf.buffer, size: buf.size, length: buf.length };
        //@ close Buffer(&buffer, _, _);
        loop {
            //@ inv platform::sockets::ServerSocket(server_socket) &*& Buffer(&buffer, _, _);
            let client_socket = server_socket.accept();
            handle_connection(&mut buffer as *mut Buffer, client_socket);
        }
    }
}
