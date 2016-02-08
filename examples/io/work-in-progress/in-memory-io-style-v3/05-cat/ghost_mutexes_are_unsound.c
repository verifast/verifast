//@ #include "ghost_mutex.gh"
//@ #include <ghost_cells.gh>

// Note: I think this also applies to ghost critical sections from <threading.h>.

/*@
predicate_ctor invar(int id)() =
  ghost_cell<int>(id, 0);

lemma void empty_lemma()
requires true;
ensures true;
{
}

predicate_ctor p1(ghost_mutex mutex, int cell)() =
  [1/2]ghost_mutex(mutex, invar(cell));

predicate false_pred() = false;

lemma void do_merge_fractions()
  requires [?f]ghost_cell<int>(?cell, ?val1) &*& [?f2]ghost_cell<int>(cell, ?val2);
  ensures [f+f2]ghost_cell(cell, val1) &*& val1 == val2;
{
}

lemma void evil()
nonghost_callers_only
requires true;
ensures false;
{
  int cell = create_ghost_cell(0);
  close invar(cell)();
  ghost_mutex mutex = create_ghost_mutex(invar(cell));
  produce_lemma_function_pointer_chunk(empty_lemma) : ghost_mutex_critical_section_t(invar(cell), p1(mutex, cell), false_pred)() {

    
    produce_lemma_function_pointer_chunk(empty_lemma) : ghost_mutex_critical_section_t(invar(cell), invar(cell), false_pred)() {
      call();
      open invar(cell)();
      ghost_cell_mutate(cell, 1);
      open invar(cell)();
      do_merge_fractions();
      assert 0 == 1; // Interesting.
    }
    {
      duplicate_lemma_function_pointer_chunk(ghost_mutex_critical_section_t);
    }
    
    
    open p1(mutex, cell)();
    
    // Inside a create_lemma_function_pointer_chunk you can call nonghost_callers_only lemmas:
    ghost_mutex_use(mutex, invar(cell), false_pred);
    
    open false_pred();
    
    call();
  }
  {
    duplicate_lemma_function_pointer_chunk(ghost_mutex_critical_section_t);
  }
  close p1(mutex, cell)();
  ghost_mutex_use(mutex, p1(mutex, cell), false_pred);
  open false_pred();
}
@*/

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  //@ evil();
  int *ptr = 0;
  *ptr = 0; // crash with green bar.
}
