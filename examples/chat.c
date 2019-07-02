#include <stdbool.h>
#include "malloc.h"
#include "lists.h"
#include "stringBuffers.h"
#include "sockets.h"
#include "threading.h"
#include "stdlib.h"
//@ #include "ghostlist.gh"

struct member {
    struct member *next;
    struct string_buffer *nick;
    struct writer *writer;
};

/*@
predicate member(struct member* member) =
    member->nick |-> ?nick &*& [1/2]member->writer |-> ?writer &*& string_buffer(nick, _) &*& writer(writer) &*& malloc_block_member(member);
@*/

struct room {
    struct member *members;
    //@ int ghost_list_id;
};

/*@
predicate room(struct room* room) =
    room->members |-> ?membersList &*& [?f]room->ghost_list_id |-> ?id &*&
    lseg(membersList, 0, ?members, member) &*&
    ghost_list(id, members) &*& malloc_block_room(room);
@*/

struct room *create_room()
    //@ requires emp;
    //@ ensures room(result);
{
    struct room *room = 0;
    room = malloc(sizeof(struct room));
    if (room == 0) {
        abort();
    }
    room->members = 0;
    //@ close lseg(0, 0, nil, member);
    //@ int i = create_ghost_list();
    //@ room->ghost_list_id = i;
    //@ close room(room);
    return room;
}

bool room_has_member(struct room *room, struct string_buffer *nick)
    //@ requires room(room) &*& string_buffer(nick, _);
    //@ ensures room(room) &*& string_buffer(nick, _);
{
    //@ open room(room);
    //@ struct member *membersList = room->members;
    //@ assert lseg(membersList, 0, ?members, member);
    struct member *iter = room->members;
    bool hasMember = false;
    //@ close lseg(membersList, membersList, nil, member);
    while (iter != 0 && !hasMember)
        /*@
        invariant
            string_buffer(nick, _) &*&
            lseg(membersList, iter, ?members0, member) &*& lseg(iter, 0, ?members1, member) &*& members == append(members0, members1);
        @*/
    {
        //@ open lseg(iter, 0, members1, member);
        //@ open member(iter);
        hasMember = string_buffer_equals(iter->nick, nick);
        //@ close member(iter);
        iter = *(void **)(void *)iter;
        //@ lseg_add(membersList);
    }
    //@ lseg_append_final(membersList);
    //@ close room(room);
    return hasMember;
}

void room_broadcast_message(struct room *room, struct string_buffer *message)
    //@ requires room(room) &*& string_buffer(message, _);
    //@ ensures room(room) &*& string_buffer(message, _);
{
    //@ open room(room);
    struct member *iter = room->members;
    //@ assert lseg(?list, 0, ?ms, member);
    //@ close lseg(list, list, nil, member);
    while (iter != 0)
        //@ invariant string_buffer(message, _) &*& lseg(list, iter, ?ms0, member) &*& lseg(iter, 0, ?ms1, member) &*& ms == append(ms0, ms1);
    {
        //@ open lseg(iter, 0, ms1, member);
        //@ open member(iter);
        writer_write_string_buffer(iter->writer, message);
        writer_write_string(iter->writer, "\r\n");
        //@ close member(iter);
        iter = *(void **)(void *)iter;
        //@ lseg_add(list);
    }
    //@ lseg_append_final(list);
    //@ close room(room);
}

struct session {
    struct room *room;
    struct lock *room_lock;
    struct socket *socket;
};

/*@

predicate_ctor room_ctor(struct room *room)() =
    room(room);

predicate session(struct session *session) =
    session->room |-> ?room &*& session->room_lock |-> ?roomLock &*& session->socket |-> ?socket &*& malloc_block_session(session)
        &*& [_]lock(roomLock, _, room_ctor(room)) &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

@*/

struct session *create_session(struct room *room, struct lock *roomLock, struct socket *socket)
    //@ requires [_]lock(roomLock, _, room_ctor(room)) &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);
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
    /*@
    requires
        locked(roomLock, ?roomLockId, room_ctor(room), currentThread, _) &*& lockset(currentThread, cons(roomLockId, nil)) &*&
        room(room) &*& reader(reader) &*& writer(writer) &*& string_buffer(nick, _);
    @*/
    /*@
    ensures
        [_]lock(roomLock, roomLockId, room_ctor(room)) &*& lockset(currentThread, nil) &*&
        reader(reader) &*& writer(writer) &*& string_buffer(nick, _);
    @*/
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
        //@ split_fraction member_writer(member, _) by 1/2;
        //@ close member(member);
        //@ assert room->members |-> ?list &*& lseg(list, 0, ?members, @member);
        member->next = room->members;
        room->members = member;
        //@ open member_next(member, _);
        //@ close lseg(member, 0, cons(member, members), @member);
        //@ assert [_]room->ghost_list_id |-> ?id;
        //@ split_fraction room_ghost_list_id(room, id);
        //@ ghost_list_add(id, member);
        //@ close room(room);
    }
    
    //@ close room_ctor(room)();
    lock_release(roomLock);
    //@ leak [_]lock(roomLock, roomLockId, room_ctor(room));
    
    {
        bool eof = false;
        struct string_buffer *message = create_string_buffer();
        while (!eof)
            //@ invariant reader(reader) &*& string_buffer(nick, _) &*& string_buffer(message, _) &*& [_]lock(roomLock, roomLockId, room_ctor(room)) &*& lockset(currentThread, nil);
        {
            eof = reader_read_line(reader, message);
            if (eof) {
            } else {
                lock_acquire(roomLock);
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
                lock_release(roomLock);
            }
        }
        string_buffer_dispose(message);
    }
    
    lock_acquire(roomLock);
    //@ open room_ctor(room)();
    //@ open room(room);
    {
        struct member *membersList = room->members;
        //@ open room_members(room, _);
        //@ assert lseg(membersList, 0, ?members, @member);
        //@ assert [_]ghost_list_member_handle(?id, ?d);
        //@ ghost_list_member_handle_lemma(id, d);
        lseg_remove(&room->members, member);
        //@ assert pointer(&room->members, ?list);
        //@ close room_members(room, list);
        //@ assert pointer((void *)member, ?memberNext);
        //@ close member_next(member, memberNext);
    }
    //@ assert ghost_list(?id, _);
    //@ ghost_list_remove(id, member);
    //@ close room(room);
    {
        struct string_buffer *goodbyeMessage = create_string_buffer();
        string_buffer_append_string_buffer(goodbyeMessage, nick);
        string_buffer_append_string(goodbyeMessage, " left the room.");
        room_broadcast_message(room, goodbyeMessage);
        string_buffer_dispose(goodbyeMessage);
    }
    //@ close room_ctor(room)();
    lock_release(roomLock);
    
    //@ open member(member);
    string_buffer_dispose(member->nick);
    free(member);
}

/*@

predicate_family_instance thread_run_data(session_run)(void *data) = session(data);

@*/

void session_run(void *data) //@ : thread_run
    //@ requires thread_run_data(session_run)(data) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
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
    //@ open room_ctor(room)();
    //@ open room(room);
    {
        struct member *iter = room->members;
        //@ assert lseg(?membersList, 0, ?ms, member);
        //@ close lseg(membersList, membersList, nil, member);
        while (iter != 0)
            //@ invariant writer(writer) &*& lseg(membersList, iter, ?ms0, member) &*& lseg(iter, 0, ?ms1, member) &*& ms == append(ms0, ms1);
        {
            //@ open lseg(iter, 0, ms1, member);
            //@ open member(iter);
            writer_write_string_buffer(writer, iter->nick);
            writer_write_string(writer, "\r\n");
            //@ close member(iter);
            iter = *(void **)(void *)iter;
            //@ lseg_add(membersList);
        }
        //@ lseg_append_final(membersList);
    }
    //@ close room(room);
    //@ close room_ctor(room)();
    lock_release(roomLock);

    {
        struct string_buffer *nick = create_string_buffer();
        bool done = false;
        while (!done)
          //@ invariant writer(writer) &*& reader(reader) &*& string_buffer(nick, _) &*& [_]lock(roomLock, _, room_ctor(room)) &*& lockset(currentThread, nil);
        {
            writer_write_string(writer, "Please enter your nick: ");
            {
                bool eof = reader_read_line(reader, nick);
                if (eof) {
                    done = true;
                } else {
                    lock_acquire(roomLock);
                    //@ open room_ctor(room)();
                    {
                        bool hasMember = room_has_member(room, nick);
                        if (hasMember) {
                            //@ close room_ctor(room)();
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
}

int main() //@ : main
    //@ requires true;
    //@ ensures false;
{
    struct room *room = create_room();
    //@ close room_ctor(room)();
    //@ close create_lock_ghost_args(room_ctor(room), nil, nil);
    struct lock *roomLock = create_lock();
    //@ leak lock(roomLock, _, _);
    struct server_socket *serverSocket = create_server_socket(12345);

    for (;;)
        //@ invariant [_]lock(roomLock, _, room_ctor(room)) &*& server_socket(serverSocket);
    {
        struct socket *socket = server_socket_accept(serverSocket);
        struct session *session = create_session(room, roomLock, socket);
        //@ close thread_run_data(session_run)(session);
        thread_start(session_run, session);
    }
}
