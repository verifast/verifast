#ifndef IO_H
#define IO_H

// TODO: I want to put here things that does not have a body (i.e. needs a soundness proof),
//       or that remains the same always anyways (if any).
//       Find out what fits here and what not.


/*@
#define progress_t list<fixpoint(list<int>, list<int>, bool)>

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
    case id_join(left, right): return id_family(left);
  }
}
fixpoint bool id_is_split(id id) {
  switch(id){
    case id_split_left(sub): return true;
    case id_split_right(sub): return true;
    default: return false;
  }
}
fixpoint bool id_is_join(id id) {
  switch(id){
    case id_join(sub1, sub2): return true;
    default: return false;
  }
}

inductive place = no_place | place(id id, place parent1, place parent2, progress_t progress);
fixpoint id place_id(place t1) {
  switch(t1) {
    case no_place: return default_value<id>;
    case place(id, parent1, parent2, progress): return id;
  }
}
fixpoint progress_t place_progress(place t1) {
  switch(t1) {
    case no_place: return default_value<progress_t>;
    case place(id, parent1, parent2, progress): return progress;
  }
}
fixpoint place place_parent1(place t1) {
  switch(t1) {
    case no_place: return default_value<place>;
    case place(id, parent1, parent2, progress): return parent1;
  }
}
fixpoint place place_parent2(place t1) {
  switch(t1) {
    case no_place: return default_value<place>;
    case place(id, parent1, parent2, progress): return parent2;
  }
}
fixpoint place place_io(place t1, fixpoint(list<int>, list<int>, bool) fp) {
  return place(place_id(t1), place_parent1(t1), place_parent2(t1), cons(fp, place_progress(t1)));
}
fixpoint place place_join(place t1, place t2) {
  return place(id_join(place_id(t1), place_id(t2)), t1, t2, nil);
}

// This has two arguments (instead of one "place" argument),
// so that [1/2]progress(key, ?value1) &*& [1/2]progress(key, ?value2) implies value1==value2.
predicate progress(id key; progress_t progress);

predicate can_create_progress(id id);

lemma int create_initial_progress();
  requires true;
  ensures can_create_progress(id_init(result));

lemma void create_progress(id id);
  requires true;
  ensures progress(id, nil); // TODO: backport solution

lemma void update_progress(id key, progress_t value);
  requires progress(key, _);
  ensures progress(key, value);

predicate token(place t1) =
  [1/2]progress(place_id(t1), place_progress(t1))
  &*& id_is_split(place_id(t1)) ?
    [1/2]token(place_parent1(t1))
  : id_is_join(place_id(t1)) ?
    token(place_parent1(t1))
    &*& token(place_parent2(t1))
  : emp;

predicate split(place t1, place t2, place t3) =
  // TODO there is overlap in information: id of t1 is related to id of t2. Can this lead to issues? Can we remove some double info?
  t2 == place(id_split_left(place_id(t1)), t1, no_place, nil) &*&
  t3 == place(id_split_right(place_id(t1)), t1, no_place, nil)
  &*& [1/2]progress(place_id(t2), nil)
  &*& [1/2]progress(place_id(t3), nil);
  
// TODO: maybe make opaque to avoid construction of "wild joins"?
predicate join(place t1, place t2, place t3) =
  t1 != t2
  &*& t3 == place_join(t1, t2)
  &*& [1/2]progress(place_id(t3), nil);

lemma void split(place t1)
  requires split(t1, ?t2, ?t3) &*& token(t1);
  ensures token(t2) &*& token(t3);
{
  open split(t1, t2, t3);
  close token(t2);
  close token(t3);
}

lemma void join(place t1)
  requires join(t1, ?t2, ?t3) &*& token(t1) &*& token(t2);
  ensures token(t3);
{
  open join(t1, t2, t3);
  close token(t3);
}

@*/

#endif