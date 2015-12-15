#ifndef IO_H
#define IO_H

// TODO THIS IS A DRAFT PROTOTYPE


struct buffer;
/*@
#define trace_t list<fixpoint(list<int>, list<int>, bool)>

// id
inductive id =
  id_init(int family)
  | id_split_left(id)
  | id_split_right(id)
  | id_join(id left, id right)
;
fixpoint int id_family(id id) {
  switch(id){
    case id_init(family): return family;
    case id_split_left(sub): return id_family(sub);
    case id_split_right(sub): return id_family(sub);
    case id_join(parent_left, parent_right): return id_family(parent_left);
  }
}
fixpoint id id_parent(id id){
  switch(id){
    case id_init(family): return default_value<id>;
    case id_split_left(sub): return sub;
    case id_split_right(sub): return sub;
    case id_join(parent_left, parent_right): return parent_left;
  }
}
fixpoint id id_parent_right(id id){
  switch(id){
    case id_init(family): return default_value<id>;
    case id_split_left(sub): return sub;
    case id_split_right(sub): return sub;
    case id_join(parent_left, parent_right): return parent_right;
  }
}

// Place
inductive place = no_place | place(id id, place parent1, place parent2, trace_t trace, list<int> progress);

fixpoint id place_id(place t1) {
  switch(t1) {
    case no_place(): return default_value<id>;
    case place(id, parent1, parent2, trace, progress): return id;
  }
}
fixpoint place place_parent1(place t1) {
  switch(t1) {
    case no_place(): return default_value<place>;
    case place(id, parent1, parent2, trace, progress): return parent1;
  }
}
fixpoint place place_parent2(place t1) {
  switch(t1) {
    case no_place(): return default_value<place>;
    case place(id, parent1, parent2, trace, progress): return parent2;
  }
}
fixpoint trace_t place_trace(place t1) {
  switch(t1) {
    case no_place(): return default_value<trace_t>;
    case place(id, parent1, parent2, trace, progress): return trace;
  }
}
fixpoint list<int> place_progress(place t1) {
  switch(t1) {
    case no_place(): return default_value<list<int> >;
    case place(id, parent1, parent2, trace, progress): return progress;
  }
}


// Progress
predicate progress(id key; list<int> progress);

predicate can_create_progress(int family, list<id> used);

lemma int create_initial_progress(list<int> init_state);
  requires true;
  ensures
    progress(id_init(result), nil)
    &*& can_create_progress(result, {id_init(result)})
    &*& token_opaque(place_init(result))
    &*& invar_opaque(result, init_state);

lemma void create_progress(id id);
  requires
    can_create_progress(?family, ?used)
    &*& !mem(id, used)
    &*& id_family(id) == family;
  ensures
    progress(id, nil)
    &*& can_create_progress(family, cons(id, used));

lemma void update_progress(id key, list<int> value);
  requires progress(key, _);
  ensures progress(key, value);

// Token
predicate token(place t1) =
  token_opaque(t1)
  &*& [1/2]progress(place_id(t1), place_progress(t1));

// Opaque
predicate token_opaque(place t1);

predicate invar_opaque(int family, list<int> state);

predicate split_opaque(place t1, place t2, place t3);

lemma void split_opaque(place t1);
  requires token_opaque(t1);
  ensures token_opaque(split_place_left(t1)) &*& token_opaque(split_place_right(t1));

predicate join_opaque(place t1, place t2, place t3);

lemma void join_opaque(place t1, place t2);
  requires token_opaque(t1) &*& token_opaque(t2);
  ensures
    token_opaque(join_place(t1, t2));

lemma void io_opaque(int family, place t1, fixpoint(list<int> state1, list<int> state2, bool allowed) io_fp, list<int> state2, list<int> progress2);
  requires token_opaque(t1) &*& invar_opaque(family, ?state1) &*& true==io_fp(state1, state2);
  ensures token_opaque(place_io(t1, io_fp, progress2)) &*& invar_opaque(family, state2);

// Split and join
predicate split(int family, predicate(int, list<int>) the_invariant, struct buffer *buffer, place t1, place t2, place t3) =
  t2 == split_place_left(t1)
  &*& t3 == split_place_right(t1)
  &*& [1/2]progress(place_id(split_place_left(t1)), nil)
  &*& [1/2]progress(place_id(split_place_right(t1)), nil);

lemma void split(place t1)
  requires split(?family, ?buffer, ?the_invariant, t1, ?t2, ?t3) &*& token(t1);
  ensures token(t2) &*& token(t3);
{
  open split(_, _, _, _, _, _);
  open token(t1);
  split_opaque(t1);
  close token(split_place_left(t1));
  close token(split_place_right(t1));
  leak [1/2]progress(_, _);
}

predicate join(int family, predicate(int, list<int>) the_invariant, struct buffer *buffer, place t1, place t2, place t3) =
  t3 == join_place(t1, t2)
  &*& [1/2]progress(place_id(join_place(t1, t2)), nil);

lemma void join(place t1)
  requires join(?family, ?the_invariant, ?buffer, t1, ?t2, ?t3) &*& token(t1) &*& token(t2);
  ensures token(t3);
{
  open join(_, _, _, _, _, _);
  open token(t1);
  open token(t2);
  join_opaque(t1, t2);
  close token(t3);
  leak [1/2]progress(_, _);
  leak [1/2]progress(_, _);
}


// Most I/O actions will require a proof (of this typedef) that the invariant allows the I/O action.
typedef lemma void invar_updatable(fixpoint (list<int>, list<int>, bool) fp, place t1, predicate(int, list<int>) the_invariant, place t2)();
 requires
    the_invariant(id_family(place_id(t1)), ?state1)
    // Alternative to this exist is to have state2 in the second set of parameters and have that parameter also in empty_lemma.
    &*& exists<list<int> >(?state2)
    &*& true==fp(state1, state2)
    &*& [1/2]progress(place_id(t1), place_progress(t1))
    &*& token_opaque(t1);
  ensures
    the_invariant(id_family(place_id(t1)), state2)
    &*& [1/2]progress(place_id(t2), place_progress(t2))
    &*& token_opaque(t2);


// To create semi-anonymous lemmas using "produce_lemma_function_pointer_chunk(empty_lemma): lemma_type_t(....)(){...}"
lemma void empty_lemma()
  requires true;
  ensures true;
{
}


// Construction of new places
fixpoint place split_place_left(place t1){
  return place(
    id_split_left(place_id(t1)),
    place(place_id(t1), place_parent1(t1), place_parent2(t1), place_trace(t1), place_progress(t1)),
    no_place,
    nil,
    nil);
}
fixpoint place split_place_right(place t1){
  return place(
    id_split_right(place_id(t1)),
    place(place_id(t1), place_parent1(t1), place_parent2(t1), place_trace(t1), place_progress(t1)),
    no_place,
    nil,
    nil);
}
fixpoint place join_place(place t1, place t2){
  return place(
    id_join(place_id(t1), place_id(t2)),
    place(place_id(t1), place_parent1(t1), place_parent2(t1), place_trace(t1), place_progress(t1)),
    place(place_id(t2), place_parent1(t2), place_parent2(t2), place_trace(t1), place_progress(t2)),
    nil,
    nil);
}
fixpoint place place_io(place t1, fixpoint(list<int>, list<int>, bool) io_fp, list<int> progress){
  return place(
    place_id(t1),
    place_parent1(t1),
    place_parent2(t1),
    cons(io_fp, place_trace(t1)),
    progress);
}
fixpoint place place_init(int family){
  return place(
    id_init(family),
    no_place,
    no_place,
    nil,
    nil);
}
@*/


#endif
