/*@
typedef lemma void lemma_type();
  requires true;
  ensures true;

lemma void test()
  requires [?f]is_lemma_type(?lem);
  ensures [f]is_lemma_type(lem);
{
  duplicate_lemma_function_pointer_chunk(lem); //~
}

@*/
