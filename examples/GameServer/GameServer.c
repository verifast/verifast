#include "stdio.h"
#include "sockets.h"
#include "threading.h"
#include "stdlib.h"

struct game {
  char* name;
  struct socket* player1;
  struct socket* player2;
  struct game* next;
};

struct session {
  struct socket* socket;
  struct globals* globals;
};

struct globals {
  struct game* games;
  struct lock* games_lock;
};

void run_game(struct game* game) 
  /*@ requires game->name |-> ?name &*& game->player1 |-> ?p1 &*& game->player2 |-> ?p2 &*& game->next |-> _ &*&
               socket(p1, ?r1, ?w1) &*& reader(r1) &*& writer(w1) &*&
               socket(p2, ?r2, ?w2) &*& reader(r2) &*& writer(w2) &*&
               malloc_block_game(game) &*& chars(name, ?cs) &*& malloc_block(name, length(cs));
  @*/
  //@ ensures true;
{
  int number1;
  int number2;
  struct reader* reader1 = socket_get_reader(game->player1);
  struct writer* writer1 = socket_get_writer(game->player1);
  struct reader* reader2 = socket_get_reader(game->player2);
  struct writer* writer2 = socket_get_writer(game->player2);
  // currently, the game is rock, paper, scissors
  // (these numbers could be entered in parallel)
  bool victory = false;
  while(! victory) 
    //@ invariant reader(r1) &*& writer(w1) &*& reader(r2) &*& writer(w2);
  {
  
    writer_write_string(writer1, "Select rock (1), paper (2) or scissors (_).\r\n");
    writer_write_string(writer2, "Waiting for other player to make a choice ...\r\n");
    number1 = reader_read_nonnegative_integer(reader1);
    writer_write_string(writer2, "Select rock (1), paper (2) or scissors (_).\r\n");
    writer_write_string(writer2, "Waiting for other player to make a choice ...\r\n");
    number2 = reader_read_nonnegative_integer(reader2);
    if(number1 == number2) {
      writer_write_string(writer1, "The other player selected the same option. Try again.\r\n");
      writer_write_string(writer2, "The other player selected the same option. Try again.\r\n");
    } else if(number1 == 2 && number2 == 1 || number1 == 1 && (number2!=1 && number2 != 2) || (number1 != 1 && number1 !=2) && number2 == 2) {
      writer_write_string(writer1, "You win.\r\n");
      writer_write_string(writer2, "You lose.\r\n");
      victory = true;
    } else {
      writer_write_string(writer1, "You lose.\r\n");
      writer_write_string(writer2, "You win.\r\n");
      victory = true;
    }
  }
  socket_close(game->player1);
  socket_close(game->player2);
  free(game->name);
  free(game);
}

/*@
predicate_ctor globs(struct globals* globals)() = 
  globals->games |-> ?game &*& gamelist(game);

predicate gamelist(struct game* game) =
   game == 0 ? 
    true :
    game->player1 |-> ?s1 &*& game->player2 |-> _ &*& game->next |-> ?next &*& game->name |-> ?n &*&
    socket(s1, ?r1, ?w1) &*& reader(r1) &*& writer(w1) &*& malloc_block_game(game) &*& gamelist(next) &*&
    chars(n, ?cs) &*& malloc_block(n, length(cs)) &*& mem('\0', cs) == true;
    
predicate_family_instance thread_run_data(handle_connection)(struct session* session) =
  session->socket |-> ?s &*& socket(s, ?reader, ?writer) &*& reader(reader) &*& writer(writer) &*&
  session->globals |-> ?globals &*& [?f]globals->games_lock |-> ?l &*& [f]lock(l, ?id, globs(globals)) &*&
  malloc_block_session(session);
@*/

void handle_connection(struct session* session) //@: thread_run
  //@ requires thread_run_data(handle_connection)(session) &*& lockset(currentThread, nil);
  //@ ensures lockset(currentThread, nil);
{
  //@ open thread_run_data(handle_connection)(session);
  int choice; struct globals* globals;
  struct reader* reader = socket_get_reader(session->socket);
  struct writer* writer = socket_get_writer(session->socket);
  writer_write_string(writer, "Welcome to our Game Server!\r\n");
  writer_write_string(writer, "What do you want to do?\r\n");
  writer_write_string(writer, "1. Create a new game and wait for someone to join.\r\n");
  writer_write_string(writer, "2. Join an existing game.\r\n");
  writer_write_string(writer, "_. Quit.\r\n");
  choice = reader_read_nonnegative_integer(reader);
  if(choice == 1) {
    char* name;
    struct game* game;
    writer_write_string(writer, "Enter a name for your game.\r\n");
    name = reader_read_line_as_string(reader);
    if(name == 0) {
      abort();
    }
    game = malloc(sizeof(struct game));
    if (game == 0) {
      abort();
    }
    game->name = name;
    game->next = 0;
    game->player1 = session->socket;
    lock_acquire(session->globals->games_lock);
    //@ open globs(session->globals)();
    game->next = session->globals->games;   
    session->globals->games = game;
    writer_write_string(writer, "Game created, waiting for another player ...\r\n");
    //@ close gamelist(game);
    //@ close globs(session->globals)();
    lock_release(session->globals->games_lock);
  } else if(choice == 2) {
    writer_write_string(writer, "Joining ...\r\n");
    lock_acquire(session->globals->games_lock);
    //@ open globs(session->globals)();
    if(session->globals->games == 0) {
      // add possibility to let players pick a game from a list
      //@ close globs(session->globals)();
      lock_release(session->globals->games_lock);
      writer_write_string(writer, "Sorry, no games are available.\r\n");
      socket_close(session->socket); // player should be given the option to create a game here
    } else {
      struct game* my_game = session->globals->games;
      //@ open gamelist(my_game);
      session->globals->games = my_game->next;
      //@ close globs(session->globals)();
      lock_release(session->globals->games_lock);
      my_game->player2 = session->socket;
      writer_write_string(writer, "You have joined game ");
      writer_write_string(writer, my_game->name);
      writer_write_string(writer, " ...\r\n");
      run_game(my_game);
    }
  } else {
    writer_write_string(writer, "Bye!\r\n");
    socket_close(session->socket);
  }
  globals = session->globals;
  //@ leak [_]globals_games_lock(globals, _);
  //@ leak [_]lock(_, _, _);
  free(session);
}

int main() //@: main
  //@ requires true;
  //@ ensures true;
{
  struct lock* lock;
  struct server_socket* ss = create_server_socket(1234);
  struct globals* globals = malloc(sizeof(struct globals));
  if(globals == 0) { abort(); }
  globals->games = 0;
  //@ close gamelist(0);
  //@ close globs(globals)();
  //@ close create_lock_ghost_args(globs(globals), nil, nil);
  lock = create_lock();
  globals->games_lock = lock;
  while(true) 
    //@ invariant server_socket(ss) &*& [?f]globals->games_lock |-> lock &*& [f]lock(lock, _, globs(globals));
  {
    struct socket* socket = server_socket_accept(ss);
    struct session* session = malloc(sizeof(struct session));
    if(session == 0) abort();
    session->globals = globals;
    session->socket = socket;
    //@ split_fraction globals_games_lock(globals, lock);
    //@ close thread_run_data(handle_connection)(session);
    thread_start(handle_connection, session);
  }
}