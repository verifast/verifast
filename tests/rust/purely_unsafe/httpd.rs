struct Buffer {
    buffer: *mut u8,
    size: usize,
    length: usize,
}

/*@

pred Buffer_own(buffer: Buffer; size: usize, length: usize) =
    size == buffer.size &*& size <= 30000 &*&
    length == buffer.length &*&
    alloc_block(buffer.buffer, size) &*&
    integers_(buffer.buffer, 1, false, length, _) &*&
    integers__(buffer.buffer + length, 1, false, size - length, _);

lem_auto Buffer_own_inv()
    req Buffer_own(?buffer, ?size, ?length);
    ens Buffer_own(buffer, size, length) &*& size == buffer.size &*& length == buffer.length;
{
    open Buffer_own(buffer, size, length);
    close Buffer_own(buffer, size, length);
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
    //@ req 1 <= size &*& size < 30000;
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
    //@ req Buffer(buffer, ?size0, ?length) &*& size < 30000;
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
            //@ assert size <= 30000;
            if 30000 - (size as isize) < (*buffer).size as isize {
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
}

unsafe fn memchr(mut haystack: *const u8, mut size: usize, needle: u8) -> *const u8
//@ req [?f]integers_(haystack, 1, false, size, ?cs) &*& size <= 30000;
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

unsafe fn handle_connection(buffer: *mut Buffer, socket: platform::sockets::Socket)
//@ req Buffer(buffer, _, _) &*& platform::sockets::Socket(socket);
//@ ens Buffer(buffer, _, _);
{
    read_line(socket, buffer);
    send_str(socket, "HTTP/1.0 200 OK\r\n\r\n");
    //@ open Buffer(_, _, _);
    //@ open Buffer_own(_, _, _);
    socket.send((*buffer).buffer, (*buffer).length);
    socket.close();
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
        loop {
            //@ inv platform::sockets::ServerSocket(server_socket) &*& Buffer(&buffer, _, _);
            let client_socket = server_socket.accept();
            handle_connection(&mut buffer as *mut Buffer, client_socket);
        }
    }
}
