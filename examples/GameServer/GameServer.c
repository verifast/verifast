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
  game->player1 |-> s1 &*& socket(s1) &*&
  game->player2 |-> s2 &*& (s2 == 0 ? true : socket(s2)) &*&
  malloc_block_game(game) &*& game->next |-> next;

predicate games_lseg(struct game* from, struct game* to, int howMany) = 
  from == to ? howMany == 0 : from != 0 &*& game(from, ?s1, 0, ?next) &*& games_lseg(next, to, howMany - 1);
  
predicate_ctor lock_invariant(struct game** games_list)() =
  pointer(games_list, ?games) &*& games_lseg(games, 0, ?howmany);
@*/

struct rpc_session {
  struct socket* socket;
  int result;
};

enum rpc { rock, paper, scissors};

/*@
predicate_family_instance thread_run_pre(read_rpc)(struct rpc_session* s, any info) =
  [1/2]s->socket |-> ?socket &*&  socket(socket) &*& s->result |-> _;
  
predicate_family_instance thread_run_post(read_rpc)(struct rpc_session* s, any info) =
  [1/2]s->socket |-> ?socket &*& socket(socket) &*&
  s->result |-> ?res &*& res == rock || res == paper || res == scissors;
@*/

void read_rpc(struct rpc_session* s) //@: thread_run
  //@ requires thread_run_pre(read_rpc)(s, ?info);
  //@ ensures thread_run_post(read_rpc)(s, info);
{
  //@ open thread_run_pre(read_rpc)(s, info);
  struct socket* socket = s->socket;
  int choice;
  socket_write_string(socket, "Enter rock (0), paper (1) or scissors (2) ...\r\n");
  choice = socket_read_nonnegative_integer(socket);
  while(choice != rock && choice != paper && choice != scissors) 
    //@ invariant socket(socket);
  {
    socket_write_string(socket, "Invalid choice. Try again.\r\n");
    choice = socket_read_nonnegative_integer(socket);
  }
  socket_write_string(socket, "Waiting for other player ...\r\n");
  s->result = choice;
  //@ close thread_run_post(read_rpc)(s, info);
}

void play_game(struct game* game) 
  //@ requires game(game, ?player1, ?player2, _) &*& player2 != 0;
  //@ ensures true;
{
  //@ open game(game, _, _, _);
  struct socket* s1 = game->player1;
  struct socket* s2 = game->player2;
  int choice1; int choice2;
  bool victory = false;
  socket_write_string(s1, "A player joined your game ...\r\n");
  socket_write_string(s2, "You have joined a game ...\r\n");
  while(! victory) 
    /*@ invariant socket(s1) &*& socket(s2) &*&
        game->player1 |-> s1 &*& game->player2 |-> s2; @*/
  {
    struct rpc_session* rpc_s1 = malloc(sizeof(struct rpc_session));
    struct rpc_session* rpc_s2 = malloc(sizeof(struct rpc_session));
    struct thread* t1; struct thread* t2;
    if(rpc_s1 == 0 || rpc_s2 == 0) abort();
    rpc_s1->socket = game->player1;
    rpc_s2->socket = game->player2;
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
      socket_write_string(s1, "The other player made the same choice. Try Again.\r\n");
      socket_write_string(s2, "The other player made the same choice. Try Again.\r\n");
    } else if(choice1 == rock && choice2 == scissors || choice1 == paper && choice2 == rock || choice1 == scissors && choice2 == paper) {
      socket_write_string(s1, "You win ...\r\n");
      socket_write_string(s2, "You lose ...\r\n");
      victory = true;
    } else {
      socket_write_string(s2, "You win ...\r\n");
      socket_write_string(s1, "You lose ...\r\n");
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

void create_game(struct socket* socket, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket) &*& [?f]lock(games_lock, ?id, lock_invariant(games_list));
  //@ ensures true;
{
  struct game* new_game; struct game* current;
  struct string_buffer * name = create_string_buffer();
  socket_write_string(socket, "Enter a name for your game ...\r\n");
  socket_read_line(socket, name);
  socket_write_string(socket, "Waiting for another player to join ...\r\n");
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
                    current->next |-> ?next &*& current->player1 |-> ?s1 &*& socket(s1) &*&
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
  requires socket(?socket);
  ensures socket(socket) &*& socket != 0; 
@*/

void show_main_menu(struct socket* socket, struct lock* games_lock, struct game** games_list);
  //@ requires socket(socket) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;

void join_random_game(struct socket* socket, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;
{
  lock_acquire(games_lock);
  //@ open lock_invariant(games_list)();
  if(*games_list == 0) {
    //@ close lock_invariant(games_list)();
    lock_release(games_lock);
    socket_write_string(socket, "No games available for joining.\r\n");
    show_main_menu(socket, games_lock, games_list);
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

void show_games(struct socket* socket, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;
{
  lock_acquire(games_lock);
  //@ open lock_invariant(games_list)();
  if(* games_list == 0) {
    //@ close lock_invariant(games_list)();
    lock_release(games_lock);
    socket_write_string(socket, "No games found.");
    show_main_menu(socket, games_lock, games_list);
  } else {
    //@ struct game* head = *games_list;
    struct game* current = *games_list;
    //@ close games_lseg(head, current, 0);
    socket_write_string(socket, "The following games are available for joining: \r\n");
    while(current != 0)
      //@ invariant games_lseg(head, current, _) &*& games_lseg(current, 0, _) &*& socket(socket);
    {
      //@ assert games_lseg(current, 0, ?howMany2);
      //@ open games_lseg(current, 0, _);
      //@ assert game(current, ?s, 0, ?next);
      //@ open game(current, _, _, next);
      socket_write_string_buffer(socket, current->name);
      socket_write_string(socket, "\r\n");
      //@ struct game* old_current = current;
      current = current->next;
      //@ close game(old_current, s, 0, next);
      /*@ 
      if(current == 0) {
        close games_lseg(old_current, 0, howMany2);
        close games_lseg(current, current, 0);
        lseg_append_lemma(head);
      } else {
        open games_lseg(current, 0, _);
        assert game(current, ?s2, 0, ?next2);
        open game(current, s2, 0, next2);
        add_last_lemma(head);
        close game(current, s2, 0, next2);
        close games_lseg(current, 0, howMany2 - 1);
      }
      @*/
    }
    //@ close lock_invariant(games_list)();
    //@ open games_lseg(current, 0, _);
    lock_release(games_lock);
    show_main_menu(socket, games_lock, games_list);
  }
}

void show_main_menu(struct socket* socket, struct lock* games_lock, struct game** games_list) 
  //@ requires socket(socket) &*& [?f]lock(games_lock, _, lock_invariant(games_list));
  //@ ensures true;
{
  int choice;
  socket_write_string(socket, "1. Create a new game and wait for another player to join ...\r\n");
  socket_write_string(socket, "2. Join a random game ...\r\n");
  socket_write_string(socket, "3. Show all games waiting for opponent ...\r\n");
  socket_write_string(socket, "_. Quit ...\r\n");
  
  choice = socket_read_nonnegative_integer(socket);
  if(choice == 1) {
    create_game(socket, games_lock, games_list);
  } else if(choice == 2) {
    join_random_game(socket, games_lock, games_list);
  } else if(choice == 3) {
    show_games(socket, games_lock, games_list);
  } else {
    socket_close(socket);
    //@ leak [f]lock(_, _, _);
  }
}

/*@
predicate_family_instance thread_run_pre(handle_connection)(struct session* session, any info) = 
  session->socket |-> ?s &*& socket(s) &*&
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
  struct lock* games_lock = session->games_lock;
  struct game** games_list = session->games_list;
  show_main_menu(socket, games_lock, games_list);
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
