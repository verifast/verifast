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
  //@ requires socket(socket) &*& [?f]lock(lock, lock_invariant(games));
  //@ ensures [f]lock(lock, lock_invariant(games));
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
  //@ requires socket(socket) &*& [?f]lock(lock, lock_invariant(games));
  //@ ensures socket(socket) &*& [f]lock(lock, lock_invariant(games));
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
  return choice;
}

void play_game(struct socket* socket1, struct socket* socket2)
  //@ requires socket(socket1) &*& socket(socket2);
  //@ ensures socket(socket1) &*& socket(socket2);
{
  bool finished = false;
  while(! finished)
    //@ invariant socket(socket1) &*& socket(socket2);
  {
    int choice1 = get_rock_paper_or_scissors(socket1);
    int choice2 = get_rock_paper_or_scissors(socket2);
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
  //@ requires socket(socket) &*& [?f]lock(lock, lock_invariant(games));
  //@ ensures socket(socket) &*& [?g]lock(lock, lock_invariant(games));
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
    //@ split_fraction lock(_, _);
    //@ close thread_run_pre(start_session)(session);
    thread_start(start_session, session);
    //@ leak thread(_, _, _);
    free(joined_game);
  }
}

void main_menu(struct socket* socket, struct lock* lock, struct game** games) 
  //@ requires socket(socket) &*& [?f]lock(lock, lock_invariant(games));
  //@ ensures true;
{
  bool quit = false;
  while(! quit) 
    //@ invariant quit ? true : socket(socket) &*& [?g]lock(lock, lock_invariant(games));
  {
    int choice = 0;
    socket_write_string(socket, "What would you like to do?\r\n");
    socket_write_string(socket, "1. Create a new game.\r\n");
    socket_write_string(socket, "2. Show all available games.\r\n");
    socket_write_string(socket, "3. Join an existing game.\r\n");
    socket_write_string(socket, "4. Quit.\r\n");
    choice = socket_read_nonnegative_integer(socket);
    if(choice == 1) {
      create_game(socket, lock, games);
      quit = true;
      //@ assert [?g]lock(lock, lock_invariant(games));
      //@ leak [g]lock(_, _);
    } else if (choice == 2) {
      show_games(socket, lock, games);
    } else if (choice == 3) {
      join_game(socket, lock, games);
    } else if (choice == 4) {
      socket_write_string(socket, "Bye!\r\n");
      socket_close(socket);
      //@ assert [?g]lock(lock, lock_invariant(games));
      //@ leak [g]lock(_, _);
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
  session->lock |-> ?lock &*& [?f]lock(lock, lock_invariant(games)) &*&
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
  ss = create_server_socket(1234);
  while(true)
    //@ invariant server_socket(ss) &*& [?f]lock(lock, lock_invariant(games));
  {
    struct socket* socket = server_socket_accept(ss);
    struct session* session = malloc(sizeof(struct session));
    if(session == 0) abort();
    session->socket = socket;
    session->lock = lock;
    session->games = games;
    //@ split_fraction lock(lock, lock_invariant(games));
    //@ close thread_run_pre(start_session)(session);
    thread_start(start_session, session);
    //@ leak thread(_, _, _);
  }
  return 0;
}

