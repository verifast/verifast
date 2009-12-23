#include "stdio.h"
#include "sockets.h"
#include "threading.h"
#include "stdlib.h"

struct game {
  struct string_buffer* name;
  struct socket* player1;
  struct socket* player2;
  struct game* next;
};

struct session {
  struct socket* socket;
  struct lock* games_lock;
  struct game** games_list;
};

/*@
predicate game(struct game* game, struct socket* s1, struct socket* s2, struct game* next) =
  game != 0 &*& game->name |-> ?name &*& string_buffer(name) &*& 
  game->player1 |-> s1 &*& socket(s1, ?r1, ?w1) &*& reader(r1) &*& writer(w1) &*&
  game->player2 |-> s2 &*& (s2 == 0 ? true : socket(s2, ?r2, ?w2) &*& reader(r2) &*& writer(w2)) &*&
  malloc_block_game(game) &*& game->next |-> next;

predicate games_lseg(struct game* from, struct game* to, int howMany) = 
  from == to ? howMany == 0 : from != 0 &*& game(from, ?s1, 0, ?next) &*& games_lseg(next, to, howMany - 1);
  
predicate_ctor lock_invariant(struct game** games_list)() =
  pointer(games_list, ?games) &*& games_lseg(games, 0, ?howmany);
@*/

struct rpc_session {
  struct socket* socket;
  int result;
  //@ struct reader* reader;
  //@ struct writer* writer;
};

enum rpc { rock, paper, scissors};

/*@
predicate_family_instance thread_run_pre(read_rpc)(struct rpc_session* s, any info) =
  [1/2]s->socket |-> ?socket &*& [1/2]s->writer |-> ?writer &*& [1/2]s->reader |-> ?reader &*&
  socket(socket, reader, writer) &*& reader(reader) &*& writer(writer) &*&
  s->result |-> _;
  
predicate_family_instance thread_run_post(read_rpc)(struct rpc_session* s, any info) =
  [1/2]s->socket |-> ?socket &*& [1/2]s->writer |-> ?writer &*& [1/2]s->reader |-> ?reader 
  &*& socket(socket, reader, writer) &*& reader(reader) &*& writer(writer) &*&
  s->result |-> ?res &*& res == rock || res == paper || res == scissors;
@*/

void read_rpc(struct rpc_session* s) //@: thread_run
  //@ requires thread_run_pre(read_rpc)(s, ?info);
  //@ ensures thread_run_post(read_rpc)(s, info);
{
  //@ open thread_run_pre(read_rpc)(s, info);
  struct writer* w = socket_get_writer(s->socket);
  struct reader* r = socket_get_reader(s->socket);
  int choice;
  writer_write_string(w, "Enter rock (0), paper (1) or scissors (2) ...\r\n");
  choice = reader_read_nonnegative_integer(r);
  while(choice != rock && choice != paper && choice != scissors) 
    //@ invariant reader(r) &*& writer(w);
  {
    writer_write_string(w, "Invalid choice. Try again.\r\n");
    choice = reader_read_nonnegative_integer(r);
  }
  writer_write_string(w, "Waiting for other player ...\r\n");
  s->result = choice;
  //@ close thread_run_post(read_rpc)(s, info);
}

void play_game(struct game* game) 
  //@ requires game(game, ?s1, ?s2, _) &*& s2 != 0;
  //@ ensures true;
{
  //@ open game(game, s1, s2, _);
  struct writer* w1 = socket_get_writer(game->player1);
  struct writer* w2 = socket_get_writer(game->player2);
  struct reader* r1 = socket_get_reader(game->player1);
  struct reader* r2 = socket_get_reader(game->player2);
  int choice1; int choice2;
  bool victory = false;
  writer_write_string(w1, "A player joined your game ...\r\n");
  writer_write_string(w2, "You have joined a game ...\r\n");
  while(! victory) 
    /*@ invariant socket(s1, r1, w1) &*& reader(r1) &*& writer(w1) &*& socket(s2, r2, w2) &*& reader(r2) &*& writer(w2) &*&
        game->player1 |-> s1 &*& game->player2 |-> s2; @*/
  {
    struct rpc_session* rpc_s1 = malloc(sizeof(struct rpc_session));
    struct rpc_session* rpc_s2 = malloc(sizeof(struct rpc_session));
    struct thread* t1; struct thread* t2;
    if(rpc_s1 == 0 || rpc_s2 == 0) abort();
    rpc_s1->socket = game->player1;
    //@ rpc_s1->reader = r1;
    //@ rpc_s1->writer = w1;
    rpc_s2->socket = game->player2;
    //@ rpc_s2->reader = r2;
    //@ rpc_s2->writer = w2;
    //@ close thread_run_pre(read_rpc)(rpc_s1, unit);
    t1 = thread_start(read_rpc, rpc_s1);
    //@ close thread_run_pre(read_rpc)(rpc_s2, unit);
    t2 = thread_start(read_rpc, rpc_s2);
    thread_join(t1);
    thread_join(t2);
    //@ open thread_run_post(read_rpc)(rpc_s1, unit);
    //@ open thread_run_post(read_rpc)(rpc_s2, unit);
    choice1 = rpc_s1->result;
    choice2 = rpc_s2->result;
    free(rpc_s1);
    free(rpc_s2);
    if(choice1 == choice2) {
      writer_write_string(w1, "The other player made the same choice. Try Again.\r\n");
      writer_write_string(w2, "The other player made the same choice. Try Again.\r\n");
    } else if(choice1 == rock && choice2 == scissors || choice1 == paper && choice2 == rock || choice1 == scissors && choice2 == paper) {
      writer_write_string(w1, "You win ...\r\n");
      writer_write_string(w2, "You lose ...\r\n");
      victory = true;
    } else {
      writer_write_string(w2, "You win ...\r\n");
      writer_write_string(w1, "You lose ...\r\n");
      victory = true;
    }
  }
  
  socket_close(game->player1);
  socket_close(game->player2);
  string_buffer_dispose(game->name);
  free(game);
}

/*@
lemma void add_last_lemma(struct game* head)
  requires games_lseg(head, ?b, ?x) &*& game(b, ?s1, 0, ?n) &*& n->next |-> ?nn;
  ensures games_lseg(head, n, x + 1) &*& n->next |-> nn;
{
  open games_lseg(head, b, x);
  open game(b, s1, 0, n);
  close game(b, s1, 0, n);
  if(head == b) {
    close games_lseg(n, n, 0);
    close games_lseg(head, n, 1);
  } else {
    assert game(head, ?ss1, 0, ?nnnn);
    open game(head, ss1, 0, nnnn);
    add_last_lemma(head->next);
    close game(head, ss1, 0, nnnn);
    close games_lseg(head, n, x + 1);
  }
}

lemma void lseg_append_lemma(struct game* head)
  requires games_lseg(head, ?b, ?x) &*& games_lseg(b, 0, ?y);
  ensures games_lseg(head, 0, x + y);
{
  open games_lseg(head, b, x);
  if(head == b) {
  } else {
    assert game(head, ?ss1, 0, ?nn);
    lseg_append_lemma(nn);
    close games_lseg(head, 0, x + y);
  }
}
@*/

void create_game(struct socket* socket, struct reader* reader, struct writer* writer, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket, reader, writer) &*& reader(reader) &*& writer(writer) &*& [?f]lock(games_lock, ?id, lock_invariant(games_list));
  //@ ensures true;
{
  struct game* new_game; struct game* current;
  struct string_buffer * name = create_string_buffer();
  writer_write_string(writer, "Enter a name for your game ...\r\n");
  reader_read_line(reader, name);
  writer_write_string(writer, "Waiting for another player to join ...\r\n");
  new_game = malloc(sizeof(struct game));
  if(new_game == 0) abort();
  new_game->player1 = socket;
  new_game->player2 = 0;
  new_game->name = name;
  new_game->next = 0;
  //@close game(new_game, socket, 0, 0);
  lock_acquire(games_lock);
  //@ open lock_invariant(games_list)();
  current = *games_list;
  if(current == 0) {
    *games_list = new_game;
    //@ open games_lseg(0, 0, _);
    //@ close games_lseg(0, 0, 0);
    //@ close games_lseg(new_game, 0, 1);
  } else {
    struct game* head = * games_list;
    //@ close games_lseg(current, current, 0);
    //@ open games_lseg(current, 0, _);
    //@ open game(current, _, _, _);
    while(current->next != 0) 
      /*@ invariant current != 0 &*& games_lseg(head, current, ?a) &*&
                    current->name |-> ?nm &*& string_buffer(nm) &*&
                    current->next |-> ?next &*& current->player1 |-> ?s1 &*& socket(s1, ?r1, ?w1) &*& reader(r1) &*& writer(w1) &*&
                    current->player2 |-> 0 &*& malloc_block_game(current) &*& games_lseg(next, 0, ?b); @*/
    {
      struct game* old_current = current;
      current = current->next;
      //@ close game(old_current, s1, 0, current);
      //@ open games_lseg(current, 0, b);
      //@ assert game(current, ?sock, ?sock2, ?nnn);
      //@ open game(current, sock, sock2, nnn);
      //@ add_last_lemma(head);
    }
    current->next = new_game;
    //@ close game(current, _, 0, new_game);
    //@ close games_lseg(0, 0, 0);
    //@ close games_lseg(new_game, 0, 1);
    //@ close games_lseg(current, 0, 2);
    //@ open games_lseg(0, 0, b);
    //@ lseg_append_lemma(head);
  }
  //@ close lock_invariant(games_list)();
  lock_release(games_lock);
  //@ leak [f]lock(games_lock, id, lock_invariant(games_list));
}

/*@
lemma_auto void socket_non_null();
  requires socket(?socket, ?r, ?w);
  ensures socket(socket, r, w) &*& socket != 0; 
@*/

void show_main_menu(struct socket* socket, struct reader* reader, struct writer* writer, struct lock* games_lock, struct game** games_list);
  //@ requires socket(socket, reader, writer) &*& reader(reader) &*& writer(writer) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;

void join_random_game(struct socket* socket, struct reader* reader, struct writer* writer, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket, reader, writer) &*& reader(reader) &*& writer(writer) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;
{
  lock_acquire(games_lock);
  //@ open lock_invariant(games_list)();
  if(*games_list == 0) {
    //@ close lock_invariant(games_list)();
    lock_release(games_lock);
    writer_write_string(writer, "No games available for joining.\r\n");
    show_main_menu(socket, reader, writer, games_lock, games_list);
  } else {
    struct game* game = *games_list;
    //@ open games_lseg(game, 0, _);
    //@ open game(game, ?s1, 0, _);
    *games_list = game->next;
    //@ close lock_invariant(games_list)();
    lock_release(games_lock);
    game->player2 = socket;
    //@ close game(game, s1, socket, _);
    play_game(game);
    //@ leak [f]lock(games_lock, _, _);
  }
}

void join_selected_game(struct socket* socket, struct reader* reader, struct writer* writer, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket, reader, writer) &*& reader(reader) &*& writer(writer) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;
{
  lock_acquire(games_lock);
  //@ open lock_invariant(games_list)();
  if(*games_list == 0) {
    //@ close lock_invariant(games_list)();
    lock_release(games_lock);
    writer_write_string(writer, "No games available for joining.\r\n");
    show_main_menu(socket, reader, writer, games_lock, games_list);
  } else {
    int choice;
    int i;
    struct game* game;
    struct game* current = *games_list;
    int count = 1;
    //@ struct game* head = current;
    //@ assert games_lseg(head, 0, ?total_length);
    //@ close games_lseg(head, head, 0);
    while(current != 0) 
      //@ invariant writer(writer) &*& games_lseg(head, current, count - 1) &*& games_lseg(current, 0, total_length - (count - 1));
    {
      writer_write_integer_as_decimal(writer, count);
      writer_write_string(writer, ". ");
      //@ open games_lseg(current, 0, total_length - (count - 1));
      //@ assert game(current, ?s1, 0, ?n);
      //@ open game(current, s1, 0, n);
      writer_write_string_buffer(writer, current->name);
      writer_write_string(writer, "\r\n");
      //@ struct game* old_current = current;
      current = current->next;
      //@ close game(old_current, s1, 0, n);
      count = count + 1;
      /*@
      if(current == 0) {
        close games_lseg(0, 0, 0);
        close games_lseg(old_current, 0, 1);
        lseg_append_lemma(head);
      } else {
        assert games_lseg(current, 0, ?clength);
        open games_lseg(current, 0, clength);
        assert game(current, ?ss, 0, ?nnn);
        open game(current, ss, 0, nnn);
        add_last_lemma(head);
        close game(current, ss, 0, nnn);
        close games_lseg(current, 0, clength);
      }
      @*/
    }
    //@ assert games_lseg(0, 0, ?zero);
    //@ open games_lseg(0, 0, zero);
    choice = reader_read_nonnegative_integer(reader);
    while(choice < 1 || choice >= count) 
      //@ invariant writer(writer) &*& reader(reader);
    {
      writer_write_string(writer, "Invalid choice. Try again.\r\n");
      choice = reader_read_nonnegative_integer(reader);
    }
    if(choice == 1) {
      game = *games_list;
      //@ assert current == 0;
      //@ open games_lseg(game, 0, total_length);
      //@ assert game(game, ?s1, 0, ?n);
      //@ open game(game, s1, 0, n);
      *games_list = game->next;
      //@ close lock_invariant(games_list)();
      lock_release(games_lock);
      game->player2 = socket;
      //@ close game(game, s1, socket, _);
      play_game(game);
      //@ leak [f]lock(_, _, _);
    } else {
      current = *games_list;
      i = 1;
      //@ close games_lseg(head, head, 0);
      while(i < choice - 1) 
        //@ invariant 0 <= i &*& i <= choice - 1 &*& games_lseg(head, current, i - 1) &*& games_lseg(current, 0, total_length - (i - 1));
      {
        //@ struct game* old_current = current;
        //@ open games_lseg(current, 0, total_length - (i - 1));
        //@ assert game(current, ?ss, 0, ?nn);
        //@ open game(current, ss, 0, nn);
        current = current->next;
        //@ close game(old_current, ss, 0, nn);
        //@ assert games_lseg(current, 0, ?m);
        //@ open games_lseg(current, 0, m);
        //@ assert game(current, ?ss2, 0, ?nn2);
        //@ open game(current, ss2, 0, nn2);
        //@ add_last_lemma(head);
        //@ close game(current, ss2,0, nn2);
        //@ close games_lseg(current,0,m);
        i = i + 1;
      }
      //@ open games_lseg(current, 0, total_length - (i - 1)); 
      //@ assert game(current, ?ss, 0, ?nn);
      //@ open game(current, ss, 0, nn);
      game = current->next;
      //@ open games_lseg(game, 0, total_length - i);
      //@ assert game(game, ?ss2, 0, ?nn2);
      //@ open game(game, ss2, 0, nn2);
      current->next = current->next->next;
      //@ close game(current, ss, 0, nn2);
      //@ close games_lseg(current, 0, total_length - i); 
      //@ lseg_append_lemma(head);
      //@ close lock_invariant(games_list)();
      lock_release(games_lock);
      game->player2 = socket;
      //@ close game(game, ss2, socket, nn2);
      play_game(game);
      //@ leak [f]lock(_, _, _);
    }
  }
}

void show_main_menu(struct socket* socket, struct reader* reader, struct writer* writer, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket, reader, writer) &*& reader(reader) &*& writer(writer) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;
{
  int choice;
  writer_write_string(writer, "1. Create a new game and wait for another player to join ...\r\n");
  writer_write_string(writer, "2. Join a random game ...\r\n");
  writer_write_string(writer, "3. Select a game from a list ...\r\n");
  writer_write_string(writer, "_. Quit ...\r\n");
  
  choice = reader_read_nonnegative_integer(reader);
  if(choice == 1) {
    create_game(socket, reader, writer, games_lock, games_list);
  } else if(choice == 2) {
    join_random_game(socket, reader, writer, games_lock, games_list);
  } else if(choice == 3) {
    join_selected_game(socket, reader, writer, games_lock, games_list);
  } else {
    socket_close(socket);
    //@ leak [f]lock(_, _, _);
  }
}

/*@
predicate_family_instance thread_run_pre(handle_connection)(struct session* session, any info) = 
  session->socket |-> ?s &*& socket(s, ?r, ?w) &*& reader(r) &*& writer(w) &*&
  session->games_lock |-> ?games_lock &*& session->games_list |-> ?games_list &*&
  [?f]lock(games_lock, _, lock_invariant(games_list)) &*& malloc_block_session(session);
  
predicate_family_instance thread_run_post(handle_connection)(struct session* session, any info) = true;
@*/

void handle_connection(struct session* session) //@: thread_run
  //@ requires thread_run_pre(handle_connection)(session, ?info);
  //@ ensures thread_run_post(handle_connection)(session, info);
{
  //@ open thread_run_pre(handle_connection)(session, info);
  struct socket* socket = session->socket;
  struct reader* reader = socket_get_reader(socket);
  struct writer* writer = socket_get_writer(socket);
  struct lock* games_lock = session->games_lock;
  struct game** games_list = session->games_list;
  show_main_menu(socket, reader, writer, games_lock, games_list);
  free(session);
  //@ close thread_run_post(handle_connection)(session, info);
}

int main() //@: main
  //@ requires true;
  //@ ensures true;
{
  struct lock* lock; struct server_socket* ss;
  struct game** games_list = malloc(sizeof(struct game*));
  if(games_list == 0) { abort(); }
  //@ chars_to_pointer(games_list);
  *games_list = 0;
  //@ close create_lock_ghost_args(lock_invariant(games_list));
  //@ close games_lseg(0, 0, 0);
  //@ close lock_invariant(games_list)();
  lock = create_lock();
  ss = create_server_socket(1234);
  
  while(true) 
    //@ invariant server_socket(ss) &*& [?g]lock(lock, _, lock_invariant(games_list));
  {
    struct thread* thread;
    struct socket* socket = server_socket_accept(ss);
    struct session* session = malloc(sizeof(struct session));
    if(session == 0) { abort(); }
    session->socket = socket;
    session->games_lock = lock;
    session->games_list = games_list;
    //@ split_fraction lock(lock, _, lock_invariant(games_list));
    //@ close thread_run_pre(handle_connection)(session, unit);
    thread = thread_start(handle_connection, session);
    //@ leak thread(thread, handle_connection, session, unit);
  }
  return 0;
}
