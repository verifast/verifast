#include "stdlib.h"
#include "sockets.h"
#include "threading.h"
#include "bool.h"

/*@
predicate games_lseg(struct game* from, struct game* to) =
  from == to ? true : from != 0 &*&
  from->name |-> ?name &*& string_buffer(name) &*& 
  from->socket |-> ?socket &*& socket(socket) &*&
  from->next |-> ?next &*& games_lseg(next, to) &*&
  malloc_block_game(from);

predicate_ctor lock_invariant(struct game** games)() = 
  pointer(games, ?head) &*& games_lseg(head, 0) &*& malloc_block(games, 4);
@*/

struct game {
  struct string_buffer* name;
  struct socket* socket;
  struct game* next;
};

struct session {
  struct socket* socket;
  struct game** games;
  struct lock* lock;
};

void start_session(struct session* session);
  //@ requires thread_run_pre(start_session)(session);
  //@ ensures thread_run_post(start_session)(session);

void create_game(struct socket* socket, struct lock* lock, struct game** games)
  //@ requires socket(socket) &*& [_]lock(lock, lock_invariant(games));
  //@ ensures [_]lock(lock, lock_invariant(games));
{
   struct string_buffer* name = create_string_buffer();
   struct game* new_game = malloc(sizeof(struct game));
   if(new_game == 0) abort();
   socket_write_string(socket, "Enter the name of your game.\r\n");
   socket_read_line(socket, name);
   new_game->name = name;
   new_game->socket = socket;
   socket_write_string(socket, "Game created, waiting for other player...\r\n");
   lock_acquire(lock);
   //@ open lock_invariant(games)();
   new_game->next = *games;
   *games = new_game;
   //@ close games_lseg(new_game, 0);
   //@ close lock_invariant(games)();
   lock_release(lock);
}

void show_games_helper(struct socket* socket, struct game* game) 
  //@ requires socket(socket) &*& games_lseg(game, 0);
  //@ ensures socket(socket) &*& games_lseg(game, 0);
{
  //@ open games_lseg(game, 0);
  if(game == 0) {
  } else {
    socket_write_string_buffer(socket, game->name);
    socket_write_string(socket, "\r\n");
    show_games_helper(socket, game->next);
  }
  //@ close games_lseg(game, 0);
}

void show_games(struct socket* socket, struct lock* lock, struct game** games)
  //@ requires socket(socket) &*& [_]lock(lock, lock_invariant(games));
  //@ ensures socket(socket) &*& [_]lock(lock, lock_invariant(games));
{
  lock_acquire(lock);
  //@ open lock_invariant(games)();
  show_games_helper(socket, *games);
  //@ close lock_invariant(games)();
  lock_release(lock);
}

enum rps { rock, paper, scissors };

int get_rock_paper_or_scissors(struct socket* socket)
  //@ requires socket(socket);
  //@ ensures socket(socket) &*& 0 <= result &*& result <= 2;
{
  int choice = -1;
  socket_write_string(socket, "Enter a rock (0), paper (1) or scissors (2).\r\n");
  choice = socket_read_nonnegative_integer(socket);
  while(choice != rock && choice != paper && choice != scissors) 
    //@ invariant socket(socket);
  {
    socket_write_string(socket, "Try again.\r\n");
    choice = socket_read_nonnegative_integer(socket);
  }
  socket_write_string(socket, "Waiting for other player ...\r\n");
  return choice;
}

struct rps_session {
  struct socket* socket;
  int result;
};

/*@
predicate_family_instance thread_run_pre(get_rock_paper_or_scissors_async)(struct rps_session* rps_session) =
  [1/2]rps_session->socket |-> ?socket &*& socket(socket) &*&
  rps_session->result |-> _;
  
predicate_family_instance thread_run_post(get_rock_paper_or_scissors_async)(struct rps_session* rps_session) =
  [1/2]rps_session->socket |-> ?socket &*& socket(socket) &*&
  rps_session->result |-> ?res &*& 0 <= res &*& res <= 2;
@*/

void get_rock_paper_or_scissors_async(struct rps_session* rps_session) //@: thread_run
  //@ requires thread_run_pre(get_rock_paper_or_scissors_async)(rps_session);
  //@ ensures thread_run_post(get_rock_paper_or_scissors_async)(rps_session);
{
  //@ open thread_run_pre(get_rock_paper_or_scissors_async)(rps_session);
  int tmp = get_rock_paper_or_scissors(rps_session->socket);
  rps_session->result = tmp;
  //@ close thread_run_post(get_rock_paper_or_scissors_async)(rps_session);
}

void play_game(struct socket* socket1, struct socket* socket2)
  //@ requires socket(socket1) &*& socket(socket2);
  //@ ensures socket(socket1) &*& socket(socket2);
{
  bool finished = false;
  while(! finished)
    //@ invariant socket(socket1) &*& socket(socket2);
  {
    int choice1; int choice2; struct thread* thread;
    struct rps_session* rps_session = malloc(sizeof(struct rps_session));
    if(rps_session == 0) abort();
    rps_session->socket = socket1;
    //@ close thread_run_pre(get_rock_paper_or_scissors_async)(rps_session);
    thread = thread_start(get_rock_paper_or_scissors_async, rps_session);
    choice2 = get_rock_paper_or_scissors(socket2);
    thread_join(thread);
    //@ open thread_run_post(get_rock_paper_or_scissors_async)(rps_session);
    choice1 = rps_session->result;
    free(rps_session); 
    if(choice1 == choice2) {
      socket_write_string(socket1, "A draw! Try again.\r\n");
      socket_write_string(socket2, "A draw! Try again.\r\n");
    } else {
      finished = true;
      if(choice1 == rock && choice2 == scissors || 
         choice1 == paper && choice2 == rock || 
         choice1 == scissors && choice2 == paper) 
      {
        socket_write_string(socket1, "You win.\r\n");
        socket_write_string(socket2, "You lose.\r\n");
      } else {
        socket_write_string(socket2, "You win.\r\n");
        socket_write_string(socket1, "You lose.\r\n");
      }
    }
  }
}

void join_game(struct socket* socket, struct lock* lock, struct game** games)
  //@ requires socket(socket) &*& [_]lock(lock, lock_invariant(games));
  //@ ensures socket(socket) &*& [_]lock(lock, lock_invariant(games));
{
  struct game* joined_game = 0;
  lock_acquire(lock);
  //@ open lock_invariant(games)();
  if(*games == 0) {
    socket_write_string(socket, "No game is available.\r\n");
    //@ close lock_invariant(games)();
    lock_release(lock);
  } else {
    struct session* session;
    joined_game = *games;
    //@ open games_lseg(joined_game, 0);
    *games = joined_game->next;
    //@ close lock_invariant(games)();
    lock_release(lock);
    socket_write_string(socket, "You have joined ");
    socket_write_string_buffer(socket, joined_game->name);
    socket_write_string(socket, ".\r\n");
    socket_write_string(joined_game->socket, "Another player joined your game.\r\n");
    string_buffer_dispose(joined_game->name);
    play_game(joined_game->socket, socket);
    session = malloc(sizeof(struct session));
    if(session == 0) abort();
    session->socket = joined_game->socket;
    session->lock = lock;
    session->games = games;
    //@ close thread_run_pre(start_session)(session);
    thread_start(start_session, session);
    //@ leak thread(_, _, _);
    free(joined_game);
  }
}

/*@
lemma void games_lseg_append_lemma(struct game* a)
  requires games_lseg(a, ?b) &*& games_lseg(b, ?c) &*& c->next |-> ?n;
  ensures games_lseg(a, c) &*& c->next |-> n;
{
  open games_lseg(a, b);
  if(a == b) {
  } else {
    games_lseg_append_lemma(a->next);
    close games_lseg(a, c);
  }
}

lemma void games_lseg_append_lemma2(struct game* a)
  requires games_lseg(a, ?b) &*& games_lseg(b, 0);
  ensures games_lseg(a, 0);
{
  open games_lseg(a, b);
  if(a == b) {
  } else {
    games_lseg_append_lemma2(a->next);
    close games_lseg(a, 0);
  }
}
@*/

// Verification of the function create_game_last is optional.
void create_game_last(struct socket* socket, struct lock* lock, struct game** games) 
  //@ requires socket(socket) &*& [_]lock(lock, lock_invariant(games));
  //@ ensures [_]lock(lock, lock_invariant(games));
{
    struct string_buffer* name = create_string_buffer();
    struct game* new_game = malloc(sizeof(struct game));
    if(new_game == 0) abort();
    socket_write_string(socket, "Enter the name of your game.\r\n");
    socket_read_line(socket, name);
    new_game->name = name;
    new_game->socket = socket;
    new_game->next = 0;
    socket_write_string(socket, "Game created, waiting for other player...\r\n");
    lock_acquire(lock);
    //@ open lock_invariant(games)();
    if(*games == 0) {
      *games = new_game;
      //@ close games_lseg(new_game, 0);
      //@ close lock_invariant(games)();
      lock_release(lock);
    } else {
      //@ struct game* head = * games;
      struct game* current = *games;
      //@ open games_lseg(head, 0);
      //@ close games_lseg(head, current);
      while(current->next != 0) 
        //@ invariant games_lseg(head, current) &*& current != 0 &*& current->socket |-> ?s &*& socket(s) &*& current->name |-> ?nm &*& current->next |-> ?next  &*& string_buffer(nm) &*& malloc_block_game(current) &*& games_lseg(next, 0);
      {
        //@ struct game* old_current = current;
        current = current->next;
        //@ open games_lseg(current, 0);
        //@ close games_lseg(current, current);
        //@ close games_lseg(old_current, current);
        //@ games_lseg_append_lemma(head);
      }
      current->next = new_game;
      //@ close games_lseg(0, 0);
      //@ close games_lseg(new_game, 0);
      //@ close games_lseg(current, 0);
      //@ games_lseg_append_lemma2(head);
      //@ open games_lseg(0, 0);
      //@ close lock_invariant(games)();
      lock_release(lock);
    }
}

void main_menu(struct socket* socket, struct lock* lock, struct game** games) 
  //@ requires socket(socket) &*& [_]lock(lock, lock_invariant(games));
  //@ ensures true;
{
  bool quit = false;
  while(! quit) 
    //@ invariant quit ? true : socket(socket) &*& [_]lock(lock, lock_invariant(games));
  {
    int choice = 0;
    socket_write_string(socket, "What would you like to do?\r\n");
    socket_write_string(socket, "1. Create a new game.\r\n");
    socket_write_string(socket, "2. Show all available games.\r\n");
    socket_write_string(socket, "3. Join an existing game.\r\n");
    socket_write_string(socket, "4. Quit.\r\n");
    socket_write_string(socket, "5. Create a new game (optional).\r\n");
    choice = socket_read_nonnegative_integer(socket);
    if(choice == 1) {
      create_game(socket, lock, games);
      quit = true;
    } else if (choice == 2) {
      show_games(socket, lock, games);
    } else if (choice == 3) {
      join_game(socket, lock, games);
    } else if (choice == 4) {
      socket_write_string(socket, "Bye!\r\n");
      socket_close(socket);
      quit = true;
    } else if (choice == 5) {
      create_game_last(socket, lock, games);
      quit = true;
    } else {
      socket_write_string(socket, "Invalid choice. Try again.\r\n");
    }
  }
}

void start_session(struct session* session) //@: thread_run
  //@ requires thread_run_pre(start_session)(session);
  //@ ensures thread_run_post(start_session)(session);
{
  //@ open thread_run_pre(start_session)(session);
  main_menu(session->socket, session->lock, session->games);
  //@ close thread_run_post(start_session)(session);
  free(session);
}

/*@
predicate_family_instance thread_run_pre(start_session)(struct session* session) =
  session->socket |-> ?socket &*& socket(socket) &*&
  session->games |-> ?games &*&
  session->lock |-> ?lock &*& [_]lock(lock, lock_invariant(games)) &*&
  malloc_block_session(session);
  
predicate_family_instance thread_run_post(start_session)(struct session* session) =
  true;
@*/



int main() //@: main
  //@ requires true;
  //@ ensures true;
{
  struct lock* lock; struct server_socket* ss;
  struct game** games = malloc(sizeof(struct game*));
  if(games == 0) abort();
  //@ chars_to_pointer(games);
  * games = 0;
  //@ close games_lseg(0, 0);
  //@ close lock_invariant(games)();
  //@ close create_lock_ghost_args(lock_invariant(games));
  lock = create_lock();
  //@ leak lock(lock, lock_invariant(games));
  ss = create_server_socket(1234);
  while(true)
    //@ invariant server_socket(ss) &*& [_]lock(lock, lock_invariant(games));
  {
    struct socket* socket = server_socket_accept(ss);
    struct session* session = malloc(sizeof(struct session));
    if(session == 0) abort();
    session->socket = socket;
    session->lock = lock;
    session->games = games;
    //@ close thread_run_pre(start_session)(session);
    thread_start(start_session, session);
    //@ leak thread(_, _, _);
  }
  return 0;
}

