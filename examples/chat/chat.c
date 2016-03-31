#include "bool.h"
#include "malloc.h"
#include "lists.h"
#include "stringBuffers.h"
#include "sockets.h"
#include "threading.h"

struct member {
    struct string_buffer *nick;
    struct writer *writer;
};

struct room {
    struct list *members;
};

struct room *create_room()
{
    struct room *room = malloc(sizeof(room));
    struct list *members = create_list();
    room->members = members;
    return room;
}

bool room_has_member(struct room *room, struct string_buffer *nick)
{
    struct list *members = room->members;
    struct iter *iter = list_create_iter(members);
    bool hasMember = false;
    bool hasNext = iter_has_next(iter);
    while (hasNext && !hasMember)
    {
        struct member *member = (struct member *)iter_next(iter);
        struct string_buffer *memberNick = member->nick;
        hasMember = string_buffer_equals(memberNick, nick);
        hasNext = iter_has_next(iter);
    }
    iter_dispose(iter);
    return hasMember;
}

void room_broadcast_message(struct room *room, struct string_buffer *senderNick, struct string_buffer *message)
{
    struct list *members = room->members;
    struct iter *iter = list_create_iter(members);
    bool hasNext = iter_has_next(iter);
    while (hasNext)
    {
        struct member *member = (struct member *)iter_next(iter);
        struct writer *memberWriter = member->writer;
        writer_write_string_buffer(memberWriter, senderNick);
        writer_write_string(memberWriter, " says: ");
        writer_write_string_buffer(memberWriter, message);
        writer_write_string(memberWriter, "\r\n");
        hasNext = iter_has_next(iter);
    }
    iter_dispose(iter);
}

void room_broadcast_goodbye_message(struct room *room, struct string_buffer *senderNick)
{
    struct list *members = room->members;
    struct iter *iter = list_create_iter(members);
    bool hasNext = iter_has_next(iter);
    while (hasNext)
    {
        struct member *member = (struct member *)iter_next(iter);
        struct writer *memberWriter = member->writer;
        writer_write_string_buffer(memberWriter, senderNick);
        writer_write_string(memberWriter, " left the room.\r\n");
        hasNext = iter_has_next(iter);
    }
    iter_dispose(iter);
}

struct session {
    struct room *room;
    struct lock *room_lock;
    struct socket *socket;
};

struct session *create_session(struct room *room, struct lock *roomLock, struct socket *socket)
{
    struct session *session = malloc(sizeof(struct session));
    session->room = room;
    session->room_lock = roomLock;
    session->socket = socket;
    return session;
}

void session_run_with_nick(struct room *room, struct lock *roomLock, struct reader *reader, struct writer *writer, struct string_buffer *nick)
{
    struct list *members = room->members;
    struct member *member = malloc(sizeof(member));
    struct string_buffer *nickCopy = string_buffer_copy(nick);
    member->nick = nickCopy;
    member->writer = writer;
    list_add(members, member);
    lock_release(roomLock);
    
    {
        bool eof = false;
        struct string_buffer *message = create_string_buffer();
        while (!eof)
        {
            eof = reader_read_line(reader, message);
            if (eof) {
            } else {
                lock_acquire(roomLock);
                room_broadcast_message(room, nick, message);
                lock_release(roomLock);
            }
        }
        string_buffer_dispose(message);
    }
    
    lock_acquire(roomLock);
    list_remove(members, member);
    room_broadcast_goodbye_message(room, nick);
    lock_release(roomLock);
    
    string_buffer_dispose(nickCopy);
}

void session_run(void *data)
{
    struct session *session = (struct session *)data;
    struct room *room = session->room;
    struct lock *roomLock = session->room_lock;
    struct socket *socket = session->socket;
    struct writer *writer = socket_get_writer(socket);
    struct reader *reader = socket_get_reader(socket);
    free(session);
    
    writer_write_string(writer, "Welcome to the chat room.\r\n");
    writer_write_string(writer, "The following members are present:\r\n");
    
    lock_acquire(roomLock);
    {
        struct list *members = room->members;
        struct iter *iter = list_create_iter(members);
        bool hasNext = iter_has_next(iter);
        while (hasNext)
        {
            struct member *member = (struct member *)iter_next(iter);
            struct string_buffer *nick = member->nick;
            writer_write_string_buffer(writer, nick);
            writer_write_string(writer, "\r\n");
            hasNext = iter_has_next(iter);
        }
        iter_dispose(iter);
    }
    lock_release(roomLock);

    {
        struct string_buffer *nick = create_string_buffer();
        bool done = false;
        while (!done)
        {
            writer_write_string(writer, "Please enter your nick: ");
            {
                bool eof = reader_read_line(reader, nick);
                if (eof) {
                    done = true;
                } else {
                    lock_acquire(roomLock);
                    {
                        bool hasMember = room_has_member(room, nick);
                        if (hasMember) {
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

int main()
{
    struct room *room = create_room();
    struct lock *roomLock = create_lock();
    struct server_socket *serverSocket = create_server_socket(12345);

    while (true)
    {
        struct socket *socket = server_socket_accept(serverSocket);
        struct session *session = create_session(room, roomLock, socket);
        thread_start(session_run, session);
    }
}
