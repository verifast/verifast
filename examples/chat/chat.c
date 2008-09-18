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
predicate memberlistWithout(listval v, struct member* member)
  requires uniqueElements(v)==true &*& switch(v) { 
             case nil: return emp; 
             case cons(h, t): return (h==member ? emp: member(h)) &*& memberlistWithout(t, member);
           }; 

lemma void memberlist2memberlistWithout(listval v, struct member* mem)
  requires memberlist(v) &*& !contains(v, mem);
  ensures memberlistWithout(v, mem);
{
  switch(v){
    case nil: open memberlist(v); close memberlistWithout(nil, mem);
    case cons(h, t):
      open memberlist(v);
      memberlist2memberlistWithout(t, mem);
      close memberlistWithout(cons(h, t), mem);
  }
}

lemma void separateMember(listval v, struct member* mem)
  requires memberlist(v) &*& contains(v, mem)==true;
  ensures memberlistWithout(v, mem) &*& member(mem);
{
  
  switch(v) {
    case nil: open memberlist(v);return;
    case cons(h, t):
      open memberlist(v);
      if(h==mem){
        memberlist2memberlistWithout(t, mem);
        close memberlistWithout(v, mem);
      } else {
        separateMember(t, mem);
        close memberlistWithout(v, mem);
      }
  }
}

lemma void memberListWithout2memberlist(listval v, struct member* mem)
  requires memberlistWithout(v, mem) &*& ! contains(v, mem);
  ensures memberlist(v);
{
  switch(v) {
    case nil: open memberlistWithout(v, mem); close memberlist(v); 
    case cons(h, t):
      open memberlistWithout(v, mem);
      if(h==mem){
      } else {
        memberListWithout2memberlist(t, mem);
        close memberlist(v);
      }
  }
}

lemma void putMemberBack(listval v, struct member* mem)
  requires memberlistWithout(v, mem) &*& contains(v, mem)==true &*& member(mem);
  ensures memberlist(v);
{
  
  switch(v) {
    case nil: open memberlistWithout(v); return;
    case cons(h, t):
      open memberlistWithout(v, mem);
      if(h==mem){
        memberListWithout2memberlist(t, mem);
        close memberlist(v);
      } else {
        putMemberBack(t, mem);
        close memberlist(v);
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
        //@ separateMember(v, member);
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
        //@ separateMember(v, member);
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
        //@ separateMember(v, member);
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

struct session *create_session(struct room *room, struct lock *roomLock, struct socket *socket)
  //@ requires emp;
  //@ ensures result->room |-> room &*& result->room_lock |-> roomLock &*& result->socket |-> socket &*& malloc_block_session(result);
{
    struct session *session = malloc(sizeof(struct session));
    session->room = room;
    session->room_lock = roomLock;
    session->socket = socket;
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
    
    list_remove(roomMembers, member);
    //@ close room(room);
    room_broadcast_goodbye_message(room, nick);
    //@ close lock_invariant(room_label)(room);
    lock_release(roomLock);
    
    string_buffer_dispose(nickCopy);
}

void session_run(void *data)
  //@ requires true;
  //@ ensures false;
{
    struct session *session = data;
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
          //@ invariant true;
        {
            struct member *member = iter_next(iter);
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
          //@ invariant true;
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
  //@ requires true;
  //@ ensures false;
{
    struct room *room = create_room();
    struct lock *roomLock = create_lock();
    struct server_socket *serverSocket = create_server_socket(12345);

    while (true)
      //@ invariant true;
    {
        struct socket *socket = server_socket_accept(serverSocket);
        struct session *session = create_session(room, roomLock, socket);
        thread_start(session_run, session);
    }
}
