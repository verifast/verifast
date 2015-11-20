//@ #include "join_body.gh"
//@ #include "token_body.gh"

/*@
lemma void join()
nonghost_callers_only
requires join(?t1, ?t2, ?t3) &*& token(?inst, t1) &*& token(inst, t2);
ensures token(inst, t3);
{
  assume(false); // XXX
}

@*/