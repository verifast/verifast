// verifast_options{ignore_unwind_paths ignore_ref_creation extern_spec:platform=../../unverified/platform/spec/lib.rsspec extern_spec:simple_mutex=../simple_mutex/spec/lib.rsspec}

use std::io::Write;

struct Buffer {
    buffer: *mut u8,
    size: usize,
    length: usize,
}

/*@

pred Buffer_(buffer: Buffer; size: usize, length: usize) =
    size == buffer.size &*& size <= isize::MAX &*&
    length == buffer.length &*&
    std::alloc::alloc_block(buffer.buffer, std::alloc::Layout::from_size_align(size, 1)) &*&
    buffer.buffer[..length] |-> ?_ &*&
    buffer.buffer[length..size] |-> _;

lem_auto Buffer__inv()
    req [?f]Buffer_(?buffer, ?size, ?length);
    ens [f]Buffer_(buffer, size, length) &*& size == buffer.size &*& length == buffer.length &*& length <= size &*& size <= isize::MAX;
{
    open Buffer_(buffer, size, length);
    close [f]Buffer_(buffer, size, length);
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
    //@ req 1 <= size &*& size <= isize::MAX;
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
    //@ req Buffer(buffer, ?size0, ?length) &*& size <= isize::MAX;
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

    unsafe fn push_buffer(buffer: *mut Buffer, other: *mut Buffer)
    //@ req Buffer(buffer, _, ?length) &*& [?f]Buffer(other, ?otherSize, ?otherLength);
    //@ ens Buffer(buffer, _, length + otherLength) &*& [f]Buffer(other, otherSize, otherLength);
    {
        Self::reserve(buffer, (*other).length);
        //@ open [1]Buffer(_, _, _);
        //@ open [1]Buffer_(_, _, _);
        //@ open [f]Buffer_(_, _, _);
        //@ array__split((*buffer).buffer + (*buffer).length, (*other).length);
        std::ptr::copy_nonoverlapping((*other).buffer, (*buffer).buffer.add((*buffer).length), (*other).length);
        //@ array_join((*buffer).buffer);
        (*buffer).length += (*other).length;
    }

    unsafe fn clone(buffer: *mut Buffer) -> Buffer
    //@ req Buffer(buffer, ?size, ?length);
    //@ ens Buffer(buffer, size, length) &*& Buffer_(result, _, length);
    {
        let mut result = Buffer::new(if (*buffer).length == 0 { 1 } else { (*buffer).length });
        Buffer::push_buffer(&mut result as *mut Buffer, buffer);
        result
    }

    unsafe fn drop(buffer: *mut Buffer)
    //@ req Buffer(buffer, _, _);
    //@ ens (*buffer).buffer |-> _ &*& (*buffer).size |-> _ &*& (*buffer).length |-> _ &*& struct_Buffer_padding(buffer);
    {
        //@ open Buffer(_, _, _);
        //@ open Buffer_(_, _, _);
        //@ array_to_array_((*buffer).buffer);
        //@ array__join((*buffer).buffer);
        std::alloc::dealloc((*buffer).buffer, std::alloc::Layout::from_size_align_unchecked((*buffer).size, 1));
    }

}

unsafe fn memchr(mut haystack: *const u8, mut size: usize, needle: u8) -> *const u8
//@ req [?f]haystack[..size] |-> ?cs &*& size <= isize::MAX;
//@ ens [f]haystack[..size] |-> cs &*& 0 <= result as usize - haystack as usize &*& result as usize - haystack as usize <= size &*& result == haystack + (result as usize - haystack as usize);
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
        //@ open array(haystack, _, _);
        if size == 0 || *haystack == needle {
            break;
        }
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

unsafe fn send_str<'a>(socket: platform::sockets::Socket, text: &'a str)
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft](text as *u8)[..text.len()] |-> ?cs;
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft](text as *u8)[..text.len()] |-> cs;
{
    socket.send(text.as_ptr(), text.len());
}

struct Connection {
    socket: platform::sockets::Socket,
    mutex: simple_mutex::Mutex,
    buffer: *mut Buffer
}

/*@

pred_ctor mutex_inv(buffer: *mut Buffer)() = Buffer(buffer, _, _);

pred Connection(connection: *mut Connection;) =
    std::alloc::alloc_block(connection as *mut u8, std::alloc::Layout::new::<Connection>()) &*&
    struct_Connection_padding(connection) &*&
    (*connection).socket |-> ?socket &*& platform::sockets::Socket(socket) &*&
    (*connection).buffer |-> ?buffer &*&
    (*connection).mutex |-> ?mutex &*& [_]simple_mutex::Mutex(mutex, mutex_inv(buffer));

@*/

unsafe fn handle_connection(connection: *mut Connection)
//@ req Connection(connection);
//@ ens true;
{
    //@ open Connection(connection);
    let socket = (*connection).socket;
    let mutex = (*connection).mutex;
    let buffer = (*connection).buffer;

    //@ open_struct(connection);
    std::alloc::dealloc(connection as *mut u8, std::alloc::Layout::new::<Connection>());

    let mut line_buffer = Buffer::new(1000);

    read_line(socket, &mut line_buffer as *mut Buffer);

    simple_mutex::Mutex::acquire(mutex);
    //@ open mutex_inv(buffer)();
    Buffer::push_buffer(buffer, &mut line_buffer as *mut Buffer);
    let mut buffer_copy = Buffer::clone(buffer);
    //@ close mutex_inv(buffer)();
    simple_mutex::Mutex::release(mutex);

    Buffer::drop(&mut line_buffer as *mut Buffer);

    send_str(socket, "HTTP/1.0 200 OK\r\n\r\n");
    //@ open Buffer_(_, _, _);
    socket.send(buffer_copy.buffer, buffer_copy.length);
    socket.close();

    Buffer::drop(&mut buffer_copy as *mut Buffer);
}

unsafe fn print<'a>(text: &'a str)
//@ req thread_token(?t) &*& [?f](text as *u8)[..text.len()] |-> ?cs;
//@ ens thread_token(t) &*& [f](text as *u8)[..text.len()] |-> cs;
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
        //@ close mutex_inv(&buffer)();
        //@ close exists(mutex_inv(&buffer));
        let mutex = simple_mutex::Mutex::new();
        //@ leak simple_mutex::Mutex(mutex, _);
        loop {
            //@ inv platform::sockets::ServerSocket(server_socket) &*& [_]simple_mutex::Mutex(mutex, mutex_inv(&buffer));
            let client_socket = server_socket.accept();

            let connection_layout = std::alloc::Layout::new::<Connection>();
            let connection = std::alloc::alloc(connection_layout) as *mut Connection;
            if connection.is_null() {
                std::alloc::handle_alloc_error(connection_layout);
            }
            //@ close_struct(connection);
            (*connection).socket = client_socket;
            (*connection).mutex = mutex;
            (*connection).buffer = &mut buffer as *mut Buffer;
            //@ produce_fn_ptr_chunk platform::threading::thread_run<*mut Connection>(handle_connection)(Connection)(data) { call(); }
            platform::threading::fork(handle_connection, connection);
        }
    }
}
