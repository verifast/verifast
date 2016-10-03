/**
 * This example illustrates that the I/O verification approach is turing
 * complete, i.e. any input/output behavior of a turing machine can be
 * expressed in a contract.
 *
 * We do not suggest to write contracts like this. This example is just
 * to illustrate that the approach is more powerful than one might expect.
 *
 * In this file, we first model the concept of a turing machine. Next,
 * we define a predicate "tm_io" that, given a turing machine as an
 * argument, expresses the permission to do the input/output the turing
 * machine does. This way, we can for any turing machine specify that a
 * C program is only allowed to perform the I/O the turing machine does.
 *
 * To make things more interesting, we make the turing machine more
 * interactive. Typically, the input of the turing machine is the input
 * on the tape, and the output of the turing machine is the output on
 * the tape and/or the final state.
 * We could restart the turing machine to make it more interactive, but
 * we choose to extend the turing machine to have an operation "write
 * to world" and "read from world", which writes the current symbol on
 * the tape to the world, and writes a symbol received from the world on
 * the tape, respectively.
 *
 * For better understanding, we give a trivial example: we verify that a
 * simple C program that just writes what it reads, only performs the
 * I/O allowed by a turing machine that only writes (to the world) what
 * it reads (from the world).
 *
 * For a version that uses less annotation features,
 * see turing_complete_lowtech.c.
 *
 */

//@#include <io.gh>
//@#include <assoclist.gh>
#include <stdio_simple.h>
/*@
inductive tm_state = tm_state(int id);

inductive tm_config = tm_config(
  tm_state state,
  list<pair<int, int> > tape,
  int tape_head_pos
);
fixpoint tm_state tm_config_get_state(tm_config config){switch(config){case tm_config(state, tape, tape_head_pos): return state;}}
fixpoint list<pair<int, int> > tm_config_get_tape(tm_config config){switch(config){case tm_config(state, tape, tape_head_pos): return tape;}}
fixpoint int tm_config_get_tape_head_pos(tm_config config){switch(config){case tm_config(state, tape, tape_head_pos): return tape_head_pos;}}
fixpoint tm_config tm_config_update(tm_config config, int read_value){
  return tm_config(
    tm_config_get_state(config),
    cons(
      pair(tm_config_get_tape_head_pos(config), read_value),
      tm_config_get_tape(config)
    ),
    tm_config_get_tape_head_pos(config)
  );
}

inductive tm_io = 
  tm_io_read
  | tm_io_write
  | tm_io_skip
;

inductive tm_action = tm_action(
  int write_on_tape,
  int tape_move, // -1, 0, 1
  tm_io io,
  tm_state state
);
fixpoint int tm_action_get_write_on_tape(tm_action tm_action){switch(tm_action){ case tm_action(write_on_tape, tape_move, io, state): return write_on_tape;}}
fixpoint int tm_action_get_tape_move(tm_action tm_action){switch(tm_action){ case tm_action(write_on_tape, tape_move, io, state): return tape_move;}}
fixpoint tm_io tm_action_get_io(tm_action tm_action){switch(tm_action){ case tm_action(write_on_tape, tape_move, io, state): return io;}}
fixpoint tm_state tm_action_get_state(tm_action tm_action){switch(tm_action){ case tm_action(write_on_tape, tape_move, io, state): return state;}}

inductive tm = tm(
  fixpoint(tm_state, int, option<tm_action>) table,
  tm_state initial_state
);
fixpoint fixpoint(tm_state, int, option<tm_action>) tm_get_table(tm tm){switch (tm){case tm(table, initial_state): return table;}}
fixpoint tm_state tm_get_initial_state(tm tm){switch (tm){case tm(table, initial_state): return initial_state;}}

fixpoint tm_config tm_get_initial_config(tm tm){
  return tm_config(
    tm_get_initial_state(tm),
    nil, // empty tape
    0 // tape_head_pos
  );
}

inductive tm_step_info = tm_step_info(
  tm_io io,
  int io_value,
  tm_config config
);
fixpoint tm_io tm_step_info_get_io(tm_step_info info){switch(info){case tm_step_info(io, io_value, config): return io;}}
fixpoint int tm_step_info_get_io_value(tm_step_info info){switch(info){case tm_step_info(io, io_value, config): return io_value;}}
fixpoint tm_config tm_step_info_get_config(tm_step_info info){switch(info){case tm_step_info(io, io_value, config): return config;}}

fixpoint option<tm_action> get_action(tm tm, tm_config config){
  return
    (tm_get_table(tm))(
      tm_config_get_state(config),
      assoc( // look up current value in tape
        tm_config_get_tape_head_pos(config),
        tm_config_get_tape(config)
      )
    )
  ;
}

fixpoint tm_step_info tm_step_(tm tm, tm_config config) {
  return switch(get_action(tm, config)){
    case some(x): return default_value<tm_step_info>;
    case none: return default_value<tm_step_info>;
  };
}

fixpoint option<tm_step_info> tm_step(tm tm, tm_config config) {
  return switch(get_action(tm, config)){
    case none: return none;
    case some(the_action):
      return some(tm_step_info(
        // io:
        tm_action_get_io( the_action ),
        
        // io_value (only relevant for write):
        assoc( // look up current value in tape
          tm_config_get_tape_head_pos(config),
          tm_config_get_tape(config)
        ),
        
        // config:
        tm_config(
        
          // state:
          tm_action_get_state( the_action ),
          
          // tape:
          cons(
            pair(tm_config_get_tape_head_pos(config), tm_action_get_write_on_tape( the_action )), // new value
            tm_config_get_tape(config) // old tape
          ),
          
          // tape_head_pos:
          tm_config_get_tape_head_pos(config) + tm_action_get_tape_move( the_action )
        )
      ));
  };
}

fixpoint t option_unpack<t>(option<t> option){
  switch(option){
    case none: return default_value<t>;
    case some(value): return value;
  }
}


/**
 * Permission to perform the IO actions as defined by the given turing machine tm
 * starting from configuration config.
 * For the initial config, use "tm_get_initial_config(tm)".
 */
copredicate tm_io(place t1, tm tm, tm_config config, place t2) =
  tm_step(tm, config) == none ?
    no_op(t1, t2)
  :
    [_]exists(?t_before)
    &*& [_]exists(?new_config)
    &*& (tm_step_info_get_io(option_unpack(tm_step(tm, config))) == tm_io_write ?
      write_char_io(t1, stdout, tm_step_info_get_io_value( option_unpack(tm_step(tm,config)) ), ?success, t_before)
      &*& new_config == tm_step_info_get_config( option_unpack(tm_step(tm,config)) )
    : tm_step_info_get_io(option_unpack(tm_step(tm, config))) == tm_io_read ?
      read_char_io(t1, stdin, ?read_value, ?success, t_before)
      &*& new_config == tm_config_update( tm_step_info_get_config( option_unpack(tm_step(tm,config)) ), read_value)
    :
      t_before == t1
    )
    &*& tm_io(t_before, tm, new_config, t2);
@*/


// -------------------------------------------------------------- \\
//           Example: a (trivial) turing machine: "cat"           \\
// -------------------------------------------------------------- \\

/*@
/**
 * Transition table of the "cat" turing machine.
 * We could also encode it as a real table, i.e. we do
 * not exploit that fixpoints are already turing-complete,
 * but writing it as a fixpoint is more compact.
 */
fixpoint option<tm_action> cat_table(tm_state state, int on_tape) {
  // state 0 = read
  // state 1 = write
  return
    state == tm_state(0) ?
      some(tm_action(
        0, // write_on_tape, ignored
        0, // tape_move
        tm_io_read,
        tm_state(1)
      ))
    : state == tm_state(1) ?
      some(tm_action(
        0, // write_on_tape, ignored
        0, // tape_move
        tm_io_write,
        tm_state(0)
      ))
    :
      none // never happens if starting from initial state
  ;
}

// The "cat" turing machine.
fixpoint tm cat_tm(){
  return tm(
    cat_table,
    tm_state(0) // initial state
  );
}
@*/

/**
 * C program that writes what it reads.
 * We verify whether this C implementation only does the
 * I/O that is allowed by the turing machine "cat_tm".
 * Note that progress is not verified, i.e. if
 * the implementation does not do any I/O and does not terminate,
 * verification will pass.
 */
void cat()
//@ requires token(?t1) &*& tm_io(t1, cat_tm(), tm_get_initial_config(cat_tm()), ?t2);
//@ ensures token(t2);
{
  while(true)
    //@ invariant token(?t1_loop) &*& tm_io(t1_loop, cat_tm(), ?config, t2) &*& tm_config_get_state(config) == tm_state(0);
  {
    //@ open tm_io(_, _, _, _);
    int c = getchar();
    //@ open tm_io(_, _, _, _);
    putchar(c);
  }
}



