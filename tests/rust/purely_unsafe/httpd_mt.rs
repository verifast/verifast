#[path = "simple_mutex.rs"]
mod simple_mutex;

struct Buffer {
    buffer: *mut u8,
    size: usize,
    length: usize,
}

/*@

pred Buffer_own(buffer: Buffer; size: usize, length: usize) =
    size == buffer.size &*& size <= isize::MAX &*&
    length == buffer.length &*&
    alloc_block(buffer.buffer, size) &*&
    integers_(buffer.buffer, 1, false, length, _) &*&
    integers__(buffer.buffer + length, 1, false, size - length, _);

lem_auto Buffer_own_inv()
    req [?f]Buffer_own(?buffer, ?size, ?length);
    ens [f]Buffer_own(buffer, size, length) &*& size == buffer.size &*& length == buffer.length &*& length <= size &*& size <= isize::MAX;
{
    open Buffer_own(buffer, size, length);
    close [f]Buffer_own(buffer, size, length);
}

pred Buffer(buffer: *Buffer; size: usize, length: usize) =
    struct_Buffer_padding(buffer) &*&
    (*buffer).buffer |-> ?buf &*&
    (*buffer).size |-> size &*&
    (*buffer).length |-> length &*&
    Buffer_own(Buffer { buffer: buf, size, length }, size, length);

@*/

impl Buffer {
    unsafe fn new(size: usize) -> Buffer
    //@ req 1 <= size &*& size <= isize::MAX;
    //@ ens Buffer_own(result, size, 0);
    {
        let layout = std::alloc::Layout::from_size_align_unchecked(size, 1);
        let buffer = std::alloc::alloc(layout);
        if buffer.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        //@ close Buffer_own(Buffer { buffer, size, length: 0}, _, _);
        Buffer { buffer, size, length: 0 }
    }

    unsafe fn reserve(buffer: *mut Buffer, mut size: usize)
    //@ req Buffer(buffer, ?size0, ?length) &*& size <= isize::MAX;
    //@ ens Buffer(buffer, ?size1, length) &*& size1 - length >= size;
    {
        //@ open Buffer(_, _, _);
        //@ open Buffer_own(_, _, _);
        //@ integers___inv();
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
            //@ integers___join(new_buffer + length);
            //@ close Buffer_own(Buffer { buffer: new_buffer, size: new_size, length }, _, _);
        }
    }

    unsafe fn push_buffer(buffer: *mut Buffer, other: *mut Buffer)
    //@ req Buffer(buffer, _, ?length) &*& [?f]Buffer(other, ?otherSize, ?otherLength);
    //@ ens Buffer(buffer, _, length + otherLength) &*& [f]Buffer(other, otherSize, otherLength);
    {
        Self::reserve(buffer, (*other).length);
        //@ open [1]Buffer(_, _, _);
        //@ open [1]Buffer_own(_, _, _);
        //@ open [f]Buffer_own(_, _, _);
        //@ integers___split((*buffer).buffer + (*buffer).length, (*other).length);
        std::ptr::copy_nonoverlapping((*other).buffer, (*buffer).buffer.add((*buffer).length), (*other).length);
        //@ integers__join((*buffer).buffer);
        (*buffer).length += (*other).length;
    }

    unsafe fn clone(buffer: *mut Buffer) -> Buffer
    //@ req Buffer(buffer, ?size, ?length);
    //@ ens Buffer(buffer, size, length) &*& Buffer_own(result, _, length);
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
        //@ open Buffer_own(_, _, _);
        //@ integers__to_integers__((*buffer).buffer);
        //@ integers___join((*buffer).buffer);
        std::alloc::dealloc((*buffer).buffer, std::alloc::Layout::from_size_align_unchecked((*buffer).size, 1));
    }

}

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
        //@ open Buffer_own(?buf, _, _);
        //@ integers___split(buf.buffer + buf.length, 1000);
        let count = socket.receive((*buffer).buffer.offset((*buffer).length as isize), RECV_BUF_SIZE);
        //@ integers__join(buf.buffer);
        //@ integers___join(buf.buffer + buf.length + count);
        if count == 0 {
            //@ close Buffer_own(buf, _, _);
            break;
        }
        (*buffer).length = offset + count;
        //@ integers__split(buf.buffer, offset);
        let nl_index = memchr((*buffer).buffer.offset(offset as isize), count, b'\n') as usize - ((*buffer).buffer as usize + offset);
        if nl_index == count {
            offset += count;
            //@ integers__join(buf.buffer);
        } else {
            (*buffer).length = offset + nl_index + 1;
            //@ integers__split(buf.buffer + offset, nl_index + 1);
            //@ integers__join(buf.buffer);
            //@ integers__to_integers__(buf.buffer + offset + nl_index + 1);
            //@ integers___join(buf.buffer + offset + nl_index + 1);
            return;
        }
    }
}

unsafe fn send_str<'a>(socket: platform::sockets::Socket, text: &'a str)
//@ req [?fs]platform::sockets::Socket(socket) &*& [?ft]integers_(text.ptr, 1, false, text.len, _);
//@ ens [fs]platform::sockets::Socket(socket) &*& [ft]integers_(text.ptr, 1, false, text.len, _);
{
    socket.send(text.as_ptr(), text.len());
}

struct Connection {
    socket: platform::sockets::Socket,
    mutex: platform::threading::Mutex,
    buffer: *mut Buffer
}

/*@

pred_ctor mutex_inv(buffer: *mut Buffer)() = Buffer(buffer, _, _);

pred Connection(connection: *mut Connection;) =
    alloc_block(connection as *mut u8, std::mem::size_of::<Connection>()) &*&
    struct_Connection_padding(connection) &*&
    (*connection).socket |-> ?socket &*& platform::sockets::Socket(socket) &*&
    (*connection).buffer |-> ?buffer &*&
    (*connection).mutex |-> ?mutex &*& [_]simple_mutex::SimpleMutex(mutex, mutex_inv(buffer));

pred handle_connection_pre(data: *mut u8;) = Connection(data as *mut Connection);

@*/

unsafe fn handle_connection(data: *mut u8)
//@ req handle_connection_pre(data);
//@ ens true;
{
    //@ open handle_connection_pre(data);
    let connection = data as *mut Connection;
    //@ open Connection(connection);
    let socket = (*connection).socket;
    let mutex = (*connection).mutex;
    let buffer = (*connection).buffer;

    //@ open_struct(connection);
    std::alloc::dealloc(data, std::alloc::Layout::new::<Connection>());

    let mut line_buffer = Buffer::new(1000);

    read_line(socket, &mut line_buffer as *mut Buffer);

    simple_mutex::SimpleMutex_acquire(mutex);
    //@ open mutex_inv(buffer)();
    Buffer::push_buffer(buffer, &mut line_buffer as *mut Buffer);
    let mut buffer_copy = Buffer::clone(buffer);
    //@ close mutex_inv(buffer)();
    simple_mutex::SimpleMutex_release(mutex);

    Buffer::drop(&mut line_buffer as *mut Buffer);

    send_str(socket, "HTTP/1.0 200 OK\r\n\r\n");
    //@ open Buffer_own(_, _, _);
    socket.send(buffer_copy.buffer, buffer_copy.length);
    socket.close();

    Buffer::drop(&mut buffer_copy as *mut Buffer);
}

fn main() {
    unsafe {
        let port: u16 = 10000;
        let server_socket = platform::sockets::Socket::listen(port);
        let mut buffer = Buffer::new(1000);
        //@ assert Buffer_own(?buf, 1000, 0);
        //@ assert buffer.buffer |-> buf.buffer &*& buffer.size |-> 1000 &*& buffer.length |-> 0;
        //@ assert buf == Buffer { buffer: buf.buffer, size: buf.size, length: buf.length };
        //@ close Buffer(&buffer, _, _);
        //@ close mutex_inv(&buffer)();
        //@ close exists(mutex_inv(&buffer));
        let mutex = simple_mutex::SimpleMutex_new();
        loop {
            //@ inv platform::sockets::ServerSocket(server_socket) &*& [_]simple_mutex::SimpleMutex(mutex, mutex_inv(&buffer));
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
            //@ produce_fn_ptr_chunk platform::threading::thread_run(handle_connection)(handle_connection_pre)(data) { call(); }
            platform::threading::fork(handle_connection, connection as *mut u8);
        }
    }
}
