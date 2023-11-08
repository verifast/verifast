/*@

predicate atomic_spaces(list<pair<list<int>, predicate()> > spaces);

@*/

/*@

typedef lemma void AtomicLong_get_op(AtomicLong l, predicate() P, predicate(long) Q)();
  requires l.state(?value) &*& P();
  ensures l.state(value) &*& Q(value);

typedef lemma void AtomicLong_get_ghost_op(AtomicLong l, predicate() pre, predicate(long) post)();
  requires atomic_spaces({}) &*& is_AtomicLong_get_op(?op, l, ?P, ?Q) &*& P() &*& pre();
  ensures atomic_spaces({}) &*& is_AtomicLong_get_op(op, l, P, Q) &*& Q(?value) &*& post(value);

typedef lemma void AtomicLong_getAndIncrement_op(AtomicLong l, predicate() P, predicate(long) Q)();
  requires l.state(?value) &*& P();
  ensures l.state(value + 1) &*& Q(value); // No overflow! Sound only if no other mutators are offered!

typedef lemma void AtomicLong_getAndIncrement_ghost_op(AtomicLong l, predicate() pre, predicate(long) post)();
  requires atomic_spaces({}) &*& is_AtomicLong_getAndIncrement_op(?op, l, ?P, ?Q) &*& P() &*& pre();
  ensures atomic_spaces({}) &*& is_AtomicLong_getAndIncrement_op(op, l, P, Q) &*& Q(?value) &*& post(value);

@*/

public final class AtomicLong {

  //@ predicate state(long value);

  public AtomicLong()
  //@ requires true;
  //@ ensures state(0);
  { throw new RuntimeException(); }

  public long get()
  //@ requires is_AtomicLong_get_ghost_op(?ghop, this, ?pre, ?post) &*& pre();
  //@ ensures post(result);
  { throw new RuntimeException(); }

  public long getAndIncrement()
  //@ requires is_AtomicLong_getAndIncrement_ghost_op(?ghop, this, ?pre, ?post) &*& pre();
  //@ ensures post(result);
  { throw new RuntimeException(); }

}
