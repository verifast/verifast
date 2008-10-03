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

/*@
predicate member(struct member* mem)
  requires mem->nick |-> ?nick &*& mem->writer |-> ?writer &*& string_buffer(nick) &*& writer(writer) &*& malloc_block_member(mem);

lemma void member_distinct(struct member *m1, struct member *m2)
  requires member(m1) &*& member(m2);
  ensures member(m1) &*& member(m2) &*& m1 != m2;
{
  open member(m1);
  open member(m2);
  close member(m2);
  close member(m1);
}
@*/

struct room {
    struct list *members;
};

/*@ 
predicate memberlist(listval v)
  requires uniqueElements(v)==true &*& switch(v) { 
             case nil: return emp; 
             case cons(h, t): return member(h) &*& memberlist(t);
           }; 
@*/

/*@ 
lemma void memberlist_member_not_contains(listval v, struct member *member)
  requires memberlist(v) &*& member(member);
  ensures memberlist(v) &*& member(member) &*& !contains(v, member);
{
  switch (v) {
    case nil:
    case cons(h, t):
      open memberlist(v);
      member_distinct(h, member);
      memberlist_member_not_contains(t, member);
      close memberlist(v);
  }
}

lemma void removeContains(listval v, void *x1, void *x2)
    requires !contains(v, x1);
    ensures  !contains(remove(v, x2), x1);
{
    switch (v) {
        case nil:
        case cons(h, t):
            if (h == x2) {
            } else {
                removeContains(t, x1, x2);
            }
    }
}

lemma void removeUniqueElements(listval v, void *x)
    requires uniqueElements(v) == true;
    ensures uniqueElements(remove(v, x)) == true;
{
    switch (v) {
        case nil:
        case cons(h, t):
            if (h == x) {
            } else {
                removeContains(t, h, x);
                removeUniqueElements(t, x);
            }
    }
}

lemma void remove_not_contains(listval v, struct member *mem)
  requires !contains(v, mem);
  ensures remove(v, mem) == v;
{
  switch (v) {
    case nil:
    case cons(h, t):
      if (h == mem) {
      } else {
      }
      remove_not_contains(t, mem);
  }
}

lemma void putMemberBack(listval v, struct member* mem)
  requires memberlist(remove(v, mem)) &*& contains(v, mem)==true &*& member(mem) &*& uniqueElements(v) == true;
  ensures memberlist(v);
{
  
  switch(v) {
    case nil: open memberlist(remove(v, mem)); return;
    case cons(h, t):
      if(h==mem){
        remove_not_contains(t, mem);
        close memberlist(v);
      } else {
        open memberlist(remove(v, mem));
        putMemberBack(t, mem);
        close memberlist(v);
      }
  }
}

lemma void memberlistRemove(listval v, struct member *mem)
    requires memberlist(v) &*& contains(v, mem) == true;
    ensures memberlist(remove(v, mem)) &*& member(mem) &*& uniqueElements(v) == true;
{
    switch (v) {
        case nil:
        case cons(h, t):
            open memberlist(v);
            if (h == mem) {
            } else {
                memberlistRemove(t, mem);
                removeUniqueElements(v, mem);
                close memberlist(remove(v, mem));
            }
    }
}

@*/

/*@
predicate room(struct room* r)
  requires r->members |-> ?list &*& list(list, ?v) &*& memberlist(v) &*& malloc_block_room(r);
@*/

struct room *create_room()
  //@ requires emp;
  //@ ensures room(result);
{
    struct room *room = malloc(sizeof(struct room));
    struct list *members = create_list();
    room->members = members;
    //@ close memberlist(nil);
    //@ close room(room);
    return room;
}

bool room_has_member(struct room *room, struct string_buffer *nick)
  //@ requires room(room) &*& string_buffer(nick);
  //@ ensures room(room) &*& string_buffer(nick);
{
    //@ open room(room);
    //@ open memberlist(?v);
    //@ close memberlist(v);
    struct list *members = room->members;
    struct iter *iter = list_create_iter(members);
    bool hasMember = false;
    bool hasNext = iter_has_next(iter);
    //@ lengthPositive(v);
    while (hasNext && !hasMember)
      //@ invariant string_buffer(nick) &*& iter(iter, members, v, ?i) &*& memberlist(v) &*& hasNext==(i<length(v)) &*& 0<=i &*& i<= length(v);
    {
        struct member *member = iter_next(iter);
        //@ containsIth(v, i);
        //@ memberlistRemove(v, member);
        //@ open member(member);
        struct string_buffer *memberNick = member->nick;
        hasMember = string_buffer_equals(memberNick, nick);
        //@ close member(member);
        //@ putMemberBack(v, member);
        hasNext = iter_has_next(iter);
    }
    iter_dispose(iter);
    //@ close room(room);
    return hasMember;
}

void room_broadcast_message(struct room *room, struct string_buffer *senderNick, struct string_buffer *message)
  //@ requires room(room) &*& string_buffer(senderNick) &*& string_buffer(message);
  //@ ensures room(room) &*& string_buffer(senderNick) &*& string_buffer(message);
{
    //@ open room(room);
    //@ open memberlist(?v);
    //@ close memberlist(v);
    struct list *members = room->members;
    struct iter *iter = list_create_iter(members);
    bool hasNext = iter_has_next(iter);
    //@ lengthPositive(v);
    while (hasNext)
      //@ invariant iter(iter, members, ?v, ?i) &*& memberlist(v) &*& string_buffer(senderNick) &*& string_buffer(message) &*& hasNext==(i<length(v)) &*& 0<=i &*& i<= length(v);
    {
        struct member *member = iter_next(iter);
        //@ containsIth(v, i);
        //@ memberlistRemove(v, member);
        //@ open member(member);
        struct writer *memberWriter = member->writer;
        writer_write_string_buffer(memberWriter, senderNick);
        writer_write_string(memberWriter, " says: ");
        writer_write_string_buffer(memberWriter, message);
        writer_write_string(memberWriter, "\r\n");
        //@ close member(member);
        //@ putMemberBack(v, member);
        hasNext = iter_has_next(iter);
    }    
    iter_dispose(iter);
    //@ close room(room);
}

void room_broadcast_goodbye_message(struct room *room, struct string_buffer *senderNick)
  //@ requires room(room) &*& string_buffer(senderNick);
  //@ ensures room(room) &*& string_buffer(senderNick);
{
    //@ open room(room);
    //@ open memberlist(?v);
    //@ close memberlist(v);
    struct list *members = room->members;
    struct iter *iter = list_create_iter(members);
    bool hasNext = iter_has_next(iter);
    //@ lengthPositive(v);
    while (hasNext)
      //@ invariant iter(iter, members, ?v, ?i) &*& memberlist(v) &*& string_buffer(senderNick) &*& hasNext==(i<length(v)) &*& 0<=i &*& i<= length(v);
    {
        struct member *member = iter_next(iter);
        //@ containsIth(v, i);
        //@ memberlistRemove(v, member);
        //@ open member(member);
        struct writer *memberWriter = member->writer;
        writer_write_string_buffer(memberWriter, senderNick);
        writer_write_string(memberWriter, " left the room.\r\n");
        //@ close member(member);
        //@ putMemberBack(v, member);
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

predicate session(struct session *session)
    requires session->room |-> ?room &*& session->room_lock |-> ?roomLock &*& session->socket |-> ?socket &*& malloc_block_session(session)
        &*& lock_permission(roomLock, room_label, room) &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

@*/

struct session *create_session(struct room *room, struct lock *roomLock, struct socket *socket)
  //@ requires lock_permission(roomLock, room_label, room) &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);
  //@ ensures session(result);
{
    struct session *session = malloc(sizeof(struct session));
    session->room = room;
    session->room_lock = roomLock;
    session->socket = socket;
    //@ close session(session);
    return session;
}

void room_label() requires emp; ensures emp; { } // Used only as a label.

/*@

predicate_family_instance lock_invariant(room_label)(void *data)
    requires room(data);

lemma void assume(bool b);
    requires emp;
    ensures b;

@*/

void session_run_with_nick(struct room *room, struct lock *roomLock, struct reader *reader, struct writer *writer, struct string_buffer *nick)
  //@ requires lock_permission(roomLock, room_label, room) &*& room(room) &*& reader(reader) &*& writer(writer) &*& string_buffer(nick);
  //@ ensures lock_permission(roomLock, room_label, room) &*& reader(reader) &*& writer(writer) &*& string_buffer(nick);
{
    //@ open room(room);
    //@ open memberlist(?v);
    //@ close memberlist(v);
    struct list *members = room->members;
    struct member *member = malloc(sizeof(struct member));
    struct string_buffer *nickCopy = string_buffer_copy(nick);
    member->nick = nickCopy;
    member->writer = writer;
    //@ close member(member);
    list_add(members, member);
    //@ memberlist_member_not_contains(v, member);
    //@ close memberlist(cons(member, v));
    //@ close room(room);
    //@ close lock_invariant(room_label)(room);
    lock_release(roomLock);
    
    {
        bool eof = false;
        struct string_buffer *message = create_string_buffer();
        while (!eof)
          //@ invariant reader(reader) &*& string_buffer(nick) &*& string_buffer(message) &*& lock_permission(roomLock, room_label, room);
        {
            eof = reader_read_line(reader, message);
            if (eof) {
            } else {
                lock_acquire(roomLock);
                //@ open lock_invariant(room_label)(room);
                room_broadcast_message(room, nick, message);
                //@ close lock_invariant(room_label)(room);
                lock_release(roomLock);
            }
        }
        string_buffer_dispose(message);
    }
    
    lock_acquire(roomLock);
    //@ open lock_invariant(room_label)(room);
    //@ open room(room);
    struct list *roomMembers = room->members;
    //@ assert list(roomMembers, ?roomMembersValue);
    //@ assume(contains(roomMembersValue, member));
    list_remove(roomMembers, member);
    //@ memberlistRemove(roomMembersValue, member);
    //@ close room(room);
    room_broadcast_goodbye_message(room, nick);
    //@ close lock_invariant(room_label)(room);
    lock_release(roomLock);
    
    //@ open member(member);
    struct string_buffer *memberNick = member->nick;
    string_buffer_dispose(memberNick);
    assert writer(?memberWriter);
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
    //@ open lock_invariant(room_label)(room);
    //@ open room(room);
    {
        struct list *members = room->members;
        //@ assert list(members, ?membersValue);
        struct iter *iter = list_create_iter(members);
        bool hasNext = iter_has_next(iter);
        //@ lengthPositive(membersValue);
        while (hasNext)
            //@ invariant writer(writer) &*& iter(iter, members, membersValue, ?i) &*& memberlist(membersValue) &*& hasNext == (i < length(membersValue)) &*& 0 <= i &*& i <= length(membersValue);
        {
            struct member *member = iter_next(iter);
            //@ containsIth(membersValue, i);
            //@ memberlistRemove(membersValue, member);
            //@ open member(member);
            struct string_buffer *nick = member->nick;
            writer_write_string_buffer(writer, nick);
            writer_write_string(writer, "\r\n");
            //@ close member(member);
            //@ putMemberBack(membersValue, member);
            hasNext = iter_has_next(iter);
        }
        iter_dispose(iter);
    }
    //@ close room(room);
    //@ close lock_invariant(room_label)(room);
    lock_release(roomLock);

    {
        struct string_buffer *nick = create_string_buffer();
        bool done = false;
        while (!done)
          //@ invariant writer(writer) &*& reader(reader) &*& string_buffer(nick) &*& lock_permission(roomLock, room_label, room);
        {
            writer_write_string(writer, "Please enter your nick: ");
            {
                bool eof = reader_read_line(reader, nick);
                if (eof) {
                    done = true;
                } else {
                    lock_acquire(roomLock);
                    //@ open lock_invariant(room_label)(room);
                    {
                        bool hasMember = room_has_member(room, nick);
                        if (hasMember) {
                            //@ close lock_invariant(room_label)(room);
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
  //@ requires true;
  //@ ensures false;
{
    struct room *room = create_room();
    //@ close lock_invariant(room_label)(room);
    struct lock *roomLock = create_lock();
    struct server_socket *serverSocket = create_server_socket(12345);

    while (true)
      //@ invariant lock_permission(roomLock, room_label, room) &*& server_socket(serverSocket);
    {
        struct socket *socket = server_socket_accept(serverSocket);
        //@ split_lock_permission(roomLock);
        struct session *session = create_session(room, roomLock, socket);
        //@ close thread_run_data(session_run)(session);
        thread_start(session_run, session);
    }
}
