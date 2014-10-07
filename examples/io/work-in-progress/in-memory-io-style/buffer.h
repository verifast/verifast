//@ #include "io/io.gh"

/*@

fixpoint list<int> list_ioactions_to_ints(list<ioaction> ioactions){
  switch(ioactions){
    case nil: return nil;
    case cons(h,t):
      return switch(h){
        case ioaction_write(v):
          return cons(v, list_ioactions_to_ints(t));
      };
  }
}
fixpoint list<ioaction> iostate_to_list(iostate iostate){
    switch(iostate){
        case iostate(ioactions): return ioactions;
    }
}


fixpoint list<int> iostate_to_int_list(iostate iostate){
  return list_ioactions_to_ints(iostate_to_list(iostate));
}

predicate syscall_iostate(iostate state);

@*/

void write(char c);
//@ requires syscall_iostate(?state);
//@ ensures syscall_iostate(iostate(cons(ioaction_write(c), iostate_to_list(state))));
