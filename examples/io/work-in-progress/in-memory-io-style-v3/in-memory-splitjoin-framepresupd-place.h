/*@
inductive place = 
  | place_init(int init_state)
  | place_io(place prev, fixpoint(int state1, int state2, bool) operation)
  | place_join(option<place> parent, place prev1, place prev2)
  | place_split_left(place prev)
  | place_split_right(place prev)
;


fixpoint option<place> get_parent(place place){
  switch(place){
    case place_init(invar): return none;
    case place_io(prev, op): return get_parent(prev);
    case place_join(parent, prev1, prev2): return parent;
    case place_split_left(prev): return some(prev);
    case place_split_right(prev): return some(prev);
  }
}

fixpoint int place_get_init_state(place t){
  switch(t){
    case place_init(invar): return invar;
    case place_io(prev, op): return default_value<int>;
    case place_join(parent, prev1, prev2): return default_value<int>;
    case place_split_left(prev): return default_value<int>;
    case place_split_right(prev): return default_value<int>;
  }
}

fixpoint fixpoint(int,int,bool) place_get_op(place t){
  switch(t){
    case place_init(invar): return default_value<fixpoint(int,int,bool)>;
    case place_io(prev, op): return op;
    case place_join(parent, prev1, prev2): return default_value<fixpoint(int,int,bool)>;
    case place_split_left(prev): return default_value<fixpoint(int,int,bool)>;
    case place_split_right(prev): return default_value<fixpoint(int,int,bool)>;
  }
}

fixpoint place place_get_prev(place t){
  switch(t){
    case place_init(invar): return default_value<place>;
    case place_io(prev, op): return prev;
    case place_join(parent, prev1, prev2): return prev1;
    case place_split_left(prev): return prev;
    case place_split_right(prev): return prev;
  }
}

fixpoint place place_get_other_prev(place t){
  switch(t){
    case place_init(invar): return default_value<place>;
    case place_io(prev, op): return default_value<place>;
    case place_join(parent, prev1, prev2): return prev2;
    case place_split_left(prev): return default_value<place>;
    case place_split_right(prev): return default_value<place>;
  }
}


inductive place_t =
  | place_init_t
  | place_io_t
  | place_join_t
  | place_split_left_t
  | place_split_right_t;

fixpoint place_t place_get_type(place t){
  switch(t){
    case place_init(invar): return place_init_t;
    case place_io(prev, op): return place_io_t;
    case place_join(parent, prev1, prev2): return place_join_t;
    case place_split_left(prev): return place_split_left_t;
    case place_split_right(prev): return place_split_right_t;
  }
}


@*/