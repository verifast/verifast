#ifndef READWRITE_TYPEDEF_IOSTYLE
#define READWRITE_TYPEDEF_IOSTYLE

//@ #include "../io/io.gh"
//@ #include "../io/helpers/prophecy.gh"
//@ #include "../io/impl/generic_io.gh"
//@ #include <quantifiers.gh>

/*@
predicate write_io(place t1, int c, place t2) =
  generic_output_io(t1, (write_io_action)(c), t2)
;

fixpoint list<int> write_io_action(
  int c,
  // --- curry here
  list<int> sigma1
){
  return append(sigma1, {c});
}
@*/
typedef void write_t
  /*@(predicate(list<int> sigma) memrepr)@*/
  (int c);
/*@ requires
  write_io(?t1, c, ?t2)
  &*& token(?inst, t1)
  &*& memrepr(?sigma)
  &*& all_tokens_invar(inst, sigma);
@*/
/*@ ensures
  token(inst, t2)
  &*& memrepr(?sigma2)
  &*& all_tokens_invar(inst, sigma2);
@*/



/*@
predicate read_io(place t1, int c, place t2) =
  generic_input_io(t1, read_io_action, c, t2)
;

fixpoint pair<list<int>, int> read_io_action(list<int> sigma1){
  return sigma1 == nil ?
    pair(nil, -1)
  :
    pair(tail(sigma1), head(sigma1));
}
@*/
typedef int read_t/*@(predicate(list<int> sigma) memrepr)@*/();
/*@ requires
  read_io(?t1, ?c, ?t2)
  &*& token(?inst, t1)
  &*& memrepr(?sigma)
  &*& all_tokens_invar(inst, sigma);
@*/
/*@ ensures
  token(inst, t2)
  &*& memrepr(?sigma2)
  &*& all_tokens_invar(inst, sigma2)
  &*& result == c;
@*/


#endif
