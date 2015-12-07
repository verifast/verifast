#ifndef IO_H
#define IO_H

// TODO: I want to put here things that does not have a body (i.e. needs a soundness proof),
//       or that remains the same always anyways (if any).
//       Find out what fits here and what not.


/*@
inductive id =
  id_init(int family)
  | id_split_left(id)
  | id_split_right(id)
  | id_join(id node_before_split)
;

fixpoint int id_family(id id) {
  switch(id){
    case id_init(family): return family;
    case id_split_left(sub): return id_family(sub);
    case id_split_right(sub): return id_family(sub);
    case id_join(parent): return id_family(parent);
  }
}

fixpoint id id_before_split(id id) {
  switch(id){
    case id_init(family): return default_value<id>;
    case id_split_left(sub): return sub;
    case id_split_right(sub): return sub;
    case id_join(parent): return parent;
  }
}

inductive place = place(id id, list<int> progress);
fixpoint id place_id(place t1) {
  switch(t1) { case place(id, progress): return id; }
}
fixpoint list<int> place_progress(place t1) {
  switch(t1) { case place(id, progress): return progress; }
}

// This has two arguments (instead of one "place" argument),
// so that [1/2]progress(key, ?value1) &*& [1/2]progress(key, ?value2) implies value1==value2.
predicate progress(id key; list<int> progress);

predicate can_create_progress(id id);

lemma int create_initial_progress();
  requires true;
  ensures can_create_progress(id_init(result));

lemma void create_progress(id id);
  requires can_create_progress(id);
  ensures
    progress(id, nil)
    &*& can_create_progress(id_split_left(id))
    &*& can_create_progress(id_split_right(id))
    &*& can_create_progress(id_join(id));

lemma void update_progress(id key, list<int> value);
  requires progress(key, _);
  ensures progress(key, value);

predicate token(place t1) =
  [1/2]progress(place_id(t1), place_progress(t1));

predicate split(place t1, place t2, place t3) =
  t2 == place(id_split_left(place_id(t1)), nil) &*&
  t3 == place(id_split_right(place_id(t1)), nil)
  &*& [1/2]progress(place_id(t2), nil)
  &*& [1/2]progress(place_id(t3), nil);
  
// TODO: maybe make opaque to avoid construction of "wild joins"?
predicate join(place t1, place t2, place t3) =
  id_before_split(place_id(t1)) == id_before_split(place_id(t2))
  &*& t1 != t2
  &*& t3 == place(id_join(id_before_split(place_id(t1))), nil)
  &*& [1/2]progress(place_id(t3), nil);

lemma void split(place t1)
  requires split(t1, ?t2, ?t3) &*& token(t1);
  ensures token(t2) &*& token(t3);
{
  leak token(t1);
  open split(t1, t2, t3);
  close token(t2);
  close token(t3);
}

lemma void join(place t1)
  requires join(t1, ?t2, ?t3) &*& token(t1) &*& token(t2);
  ensures token(t3);
{
  leak token(t1);
  leak token(t2);
  open join(t1, t2, t3);
  close token(t3);
}

@*/

#endif