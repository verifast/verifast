#include "bool.h"
#include "malloc.h"
#include "lists.h"
#include "stringBuffers.h"
#include "sockets.h"
#include "threading.h"
#include "stdlib.h"

struct member {
    struct string_buffer *nick;
    struct writer *writer;
};

/*@
predicate member(struct member* member)
    requires member->nick |-> ?nick &*& member->writer |-> ?writer &*& string_buffer(nick) &*& writer(writer) &*& malloc_block_member(member);

lemma void member_distinct(struct member *m1, struct member *m2)
    requires member(m1) &*& member(m2);
    ensures member(m1) &*& member(m2) &*& m1 != m2;
{
    open member(m1);
    open member(m2);
    close member(m2);
    close member(m1);
}

lemma void foreach_member_not_contains(listval members, struct member *member)
    requires foreach(members, @member) &*& member(member);
    ensures foreach(members, @member) &*& member(member) &*& !contains(members, member);
{
    switch (members) {
        case nil:
        case cons(member0, members0):
            open foreach(members, @member);
            member_distinct(member0, member);
            foreach_member_not_contains(members0, member);
            close foreach(members, @member);
    }
}
@*/

struct room {
    struct list *members;
};

/*@
predicate room(struct room* room)
    requires room->members |-> ?membersList &*& list(membersList, ?members) &*& foreach(members, member) &*& malloc_block_room(room);
@*/

struct room *create_room()
    //@ requires emp;
    //@ ensures room(result);
{
    struct room *room = 0;
    struct list *members = 0;
    room = malloc(sizeof(struct room));
    if (room == 0) {
        abort();
    }
    members = create_list();
    room->members = members;
    //@ close foreach(nil, member);
    //@ close room(room);
    return room;
}

bool room_has_member(struct room *room, struct string_buffer *nick)
    //@ requires room(room) &*& string_buffer(nick);
    //@ ensures room(room) &*& string_buffer(nick);
{
    //@ open room(room);
    //@ assert foreach(?members, _);
    struct list *membersList = room->members;
    struct iter *iter = list_create_iter(membersList);
    bool hasMember = false;
    bool hasNext = iter_has_next(iter);
    //@ lengthPositive(members);
    while (hasNext && !hasMember)
        //@ invariant string_buffer(nick) &*& iter(iter, membersList, members, ?i) &*& foreach(members, @member) &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
    {
        struct member *member = iter_next(iter);
        //@ containsIth(members, i);
        //@ foreach_remove(members, member);
        //@ open member(member);
        hasMember = string_buffer_equals(member->nick, nick);
        //@ close member(member);
        //@ foreach_unremove(members, member);
        hasNext = iter_has_next(iter);
    }
    iter_dispose(iter);
    //@ close room(room);
    return hasMember;
}

void room_broadcast_message(struct room *room, struct string_buffer *message)
    //@ requires room(room) &*& string_buffer(message);
    //@ ensures room(room) &*& string_buffer(message);
{
    //@ open room(room);
    //@ assert foreach(?members0, _);
    struct list *membersList = room->members;
    struct iter *iter = list_create_iter(membersList);
    bool hasNext = iter_has_next(iter);
    //@ lengthPositive(members0);
    while (hasNext)
        //@ invariant iter(iter, membersList, ?members, ?i) &*& foreach(members, @member) &*& string_buffer(message) &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
    {
        struct member *member = iter_next(iter);
        //@ containsIth(members, i);
        //@ foreach_remove(members, member);
        //@ open member(member);
        writer_write_string_buffer(member->writer, message);
        writer_write_string(member->writer, "\r\n");
        //@ close member(member);
        //@ foreach_unremove(members, member);
        hasNext = iter_has_next(iter);
    }
    iter_dispose(iter);
    //@ close room(room);
}

struct session {
    struct room *room;
    struct lock *room_lock;
    struct socket *socket;
};

/*@

predicate_ctor room_ctor(struct room *room)()
    requires room(room);

predicate session(struct session *session)
    requires session->room |-> ?room &*& session->room_lock |-> ?roomLock &*& session->socket |-> ?socket &*& malloc_block_session(session)
        &*& lock_permission(roomLock, room_ctor(room)) &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

@*/

struct session *create_session(struct room *room, struct lock *roomLock, struct socket *socket)
    //@ requires lock_permission(roomLock, room_ctor(room)) &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);
    //@ ensures session(result);
{
    struct session *session = malloc(sizeof(struct session));
    if (session == 0) {
        abort();
    }
    session->room = room;
    session->room_lock = roomLock;
    session->socket = socket;
    //@ close session(session);
    return session;
}

void session_run_with_nick(struct room *room, struct lock *roomLock, struct reader *reader, struct writer *writer, struct string_buffer *nick)
    //@ requires lock_permission(roomLock, room_ctor(room)) &*& room(room) &*& reader(reader) &*& writer(writer) &*& string_buffer(nick);
    //@ ensures lock_permission(roomLock, room_ctor(room)) &*& reader(reader) &*& writer(writer) &*& string_buffer(nick);
{
    struct member *member = 0;

    struct string_buffer *joinMessage = create_string_buffer();
    string_buffer_append_string_buffer(joinMessage, nick);
    string_buffer_append_string(joinMessage, " has joined the room.");
    room_broadcast_message(room, joinMessage);
    string_buffer_dispose(joinMessage);

    {
        struct string_buffer *nickCopy = string_buffer_copy(nick);
        //@ open room(room);
        member = malloc(sizeof(struct member));
        if (member == 0) {
            abort();
        }
        member->nick = nickCopy;
        member->writer = writer;
        //@ close member(member);
        list_add(room->members, member);
        //@ open foreach(?members, @member);
        //@ close foreach(members, @member);
        //@ foreach_member_not_contains(members, member);
        //@ close foreach(cons(member, members), @member);
        //@ close room(room);
    }
    
    //@ close room_ctor(room)();
    //@ close_lock_invariant(room_ctor(room));
    lock_release(roomLock);
    
    {
        bool eof = false;
        struct string_buffer *message = create_string_buffer();
        while (!eof)
            //@ invariant reader(reader) &*& string_buffer(nick) &*& string_buffer(message) &*& lock_permission(roomLock, room_ctor(room));
        {
            eof = reader_read_line(reader, message);
            if (eof) {
            } else {
                lock_acquire(roomLock);
                //@ open_lock_invariant();
                //@ open room_ctor(room)();
                {
                    struct string_buffer *fullMessage = create_string_buffer();
                    string_buffer_append_string_buffer(fullMessage, nick);
                    string_buffer_append_string(fullMessage, " says: ");
                    string_buffer_append_string_buffer(fullMessage, message);
                    room_broadcast_message(room, fullMessage);
                    string_buffer_dispose(fullMessage);
                }
                //@ close room_ctor(room)();
                //@ close_lock_invariant(room_ctor(room));
                lock_release(roomLock);
            }
        }
        string_buffer_dispose(message);
    }
    
    lock_acquire(roomLock);
    //@ open_lock_invariant();
    //@ open room_ctor(room)();
    //@ open room(room);
    {
        struct list *membersList = room->members;
        //@ assert list(membersList, ?members);
        //@ assume(contains(members, member));
        list_remove(membersList, member);
        //@ foreach_remove(members, member);
    }
    //@ close room(room);
    {
        struct string_buffer *goodbyeMessage = create_string_buffer();
        string_buffer_append_string_buffer(goodbyeMessage, nick);
        string_buffer_append_string(goodbyeMessage, " left the room.");
        room_broadcast_message(room, goodbyeMessage);
        string_buffer_dispose(goodbyeMessage);
    }
    //@ close room_ctor(room)();
    //@ close_lock_invariant(room_ctor(room));
    lock_release(roomLock);
    
    //@ open member(member);
    string_buffer_dispose(member->nick);
    //@ assert writer(?memberWriter);
    //@ assume(memberWriter == writer);
    free(member);
}

/*@

predicate_family_instance thread_run_data(session_run)(void *data)
    requires session(data);

@*/

void session_run(void *data) //@ : thread_run
{
    //@ open thread_run_data(session_run)(data);
    struct session *session = data;
    //@ open session(session);
    struct room *room = session->room;
    struct lock *roomLock = session->room_lock;
    struct socket *socket = session->socket;
    struct writer *writer = socket_get_writer(socket);
    struct reader *reader = socket_get_reader(socket);
    free(session);
    
    writer_write_string(writer, "Welcome to the chat room.\r\n");
    writer_write_string(writer, "The following members are present:\r\n");
    
    lock_acquire(roomLock);
    //@ open_lock_invariant();
    //@ open room_ctor(room)();
    //@ open room(room);
    {
        struct list *membersList = room->members;
        //@ assert list(membersList, ?members);
        struct iter *iter = list_create_iter(membersList);
        bool hasNext = iter_has_next(iter);
        //@ lengthPositive(members);
        while (hasNext)
            //@ invariant writer(writer) &*& iter(iter, membersList, members, ?i) &*& foreach(members, @member) &*& hasNext == (i < length(members)) &*& 0 <= i &*& i <= length(members);
        {
            struct member *member = iter_next(iter);
            //@ containsIth(members, i);
            //@ foreach_remove(members, member);
            //@ open member(member);
            writer_write_string_buffer(writer, member->nick);
            writer_write_string(writer, "\r\n");
            //@ close member(member);
            //@ foreach_unremove(members, member);
            hasNext = iter_has_next(iter);
        }
        iter_dispose(iter);
    }
    //@ close room(room);
    //@ close room_ctor(room)();
    //@ close_lock_invariant(room_ctor(room));
    lock_release(roomLock);

    {
        struct string_buffer *nick = create_string_buffer();
        bool done = false;
        while (!done)
          //@ invariant writer(writer) &*& reader(reader) &*& string_buffer(nick) &*& lock_permission(roomLock, room_ctor(room));
        {
            writer_write_string(writer, "Please enter your nick: ");
            {
                bool eof = reader_read_line(reader, nick);
                if (eof) {
                    done = true;
                } else {
                    lock_acquire(roomLock);
                    //@ open_lock_invariant();
                    //@ open room_ctor(room)();
                    {
                        bool hasMember = room_has_member(room, nick);
                        if (hasMember) {
                            //@ close room_ctor(room)();
                            //@ close_lock_invariant(room_ctor(room));
                            lock_release(roomLock);
                            writer_write_string(writer, "Error: This nick is already in use.\r\n");
                        } else {
                            session_run_with_nick(room, roomLock, reader, writer, nick);
                            done = true;
                        }
                    }
                }
            }
        }
        string_buffer_dispose(nick);
    }

    socket_close(socket);
    //@ leak lock_permission(roomLock, _);
}

int main()
    //@ requires true;
    //@ ensures false;
{
    struct room *room = create_room();
    //@ close room_ctor(room)();
    //@ close_lock_invariant(room_ctor(room));
    struct lock *roomLock = create_lock();
    struct server_socket *serverSocket = create_server_socket(12345);

    while (true)
        //@ invariant lock_permission(roomLock, room_ctor(room)) &*& server_socket(serverSocket);
    {
        struct socket *socket = server_socket_accept(serverSocket);
        //@ split_lock_permission(roomLock);
        struct session *session = create_session(room, roomLock, socket);
        //@ close thread_run_data(session_run)(session);
        thread_start(session_run, session);
    }
}
