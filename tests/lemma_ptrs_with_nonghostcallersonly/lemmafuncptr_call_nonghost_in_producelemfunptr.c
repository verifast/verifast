/**
 * Call a nonghost_callers_only lemma in a produce_lemma_function_pointer_chunk's body.
 *
 * Since lemma function pointers can be called in non-nonghost_callers_only context,
 * and if lemma function pointers can call nonghost_callers_only_lemmas, then
 * we can indirectly still call a nonghost_callers_only lemma in a
 * no-nonghost_callers_only context. This would allow to prove false.
 *
 * This example is based on lemmafuncptr_produce_invalid.c.
 */

/*@
typedef lemma void evil_lemma()();
  requires is_evil_lemma(?proof);
  ensures  false;

lemma void lemma1_orig()
nonghost_callers_only
  requires is_evil_lemma(?proof);
  ensures  false;
{  
  assert is_evil_lemma(proof);
  duplicate_lemma_function_pointer_chunk(evil_lemma);
  proof();
}

lemma void lemma1()
  requires is_evil_lemma(?proof) &*& is_evil_lemma(?proof2);
  ensures  false;
{  
  assert is_evil_lemma(proof);
  proof();
}

lemma void lemma2()
  nonghost_callers_only
  requires true;
  ensures false;
{
  produce_lemma_function_pointer_chunk(lemma1) : evil_lemma()(){
    duplicate_lemma_function_pointer_chunk(evil_lemma); //~  <-- should fail
    call();
  }{
    assert is_evil_lemma(?proof);
    duplicate_lemma_function_pointer_chunk(evil_lemma);
    proof();
  };
}


@*/

int main() //@ : main
  //@ requires true;
  //@ ensures false;
{
  //@ lemma2();
}

