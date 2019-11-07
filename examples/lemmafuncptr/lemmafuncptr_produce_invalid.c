/*@

typedef lemma void evil_lemma()();
  requires is_evil_lemma(?proof);
  ensures  false;

lemma void lemma1()
  nonghost_callers_only
  requires is_evil_lemma(?proof);
  ensures  false;
{  
  assert is_evil_lemma(proof);
  duplicate_lemma_function_pointer_chunk(evil_lemma);
  proof();
}

@*/


int main()
  //@ requires true;
  //@ ensures false;
{
  //@ produce_lemma_function_pointer_chunk(lemma1) : evil_lemma()(){ call(); }; //~
  //@ lemma1();
}

