/*@

predicate pred_out() = true;

typedef lemma void lemma_type();
  requires true;
  ensures pred_out();

lemma void test()
  requires [?f]is_lemma_type(?lem);
  ensures [f]is_lemma_type(lem) &*& pred_out();
{
  lem(); //~
}

@*/
