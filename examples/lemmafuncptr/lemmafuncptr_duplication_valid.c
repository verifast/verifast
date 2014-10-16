/*@
typedef lemma void lemma_type1()();
  requires true;
  ensures true;
typedef lemma int lemma_type2()(bool arg1, int arg2);
  requires true;
  ensures result >= 6;
typedef lemma void lemma_type3()();
  requires exists<int>(?i);
  ensures  exists<bool>(?b);
typedef lemma void lemma_type4(fixpoint(bool, int) targ1, fixpoint(bool, int) targ2)
                              (bool arg1, int arg2);
  requires true;
  ensures  true;
@*/

void test()
  /*@ requires [?f1]is_lemma_type1(?lem1) &*& 
               [?f2]is_lemma_type2(?lem2) &*& 
               [?f3]is_lemma_type3(?lem3) &*& 
               [?f4]is_lemma_type4(?targ1, ?targ2, ?lem4); @*/
  /*@ ensures  [f1]is_lemma_type1(lem1) &*& is_lemma_type1(lem1) &*& 
               [f2]is_lemma_type2(lem2) &*& is_lemma_type2(lem2) &*& 
               [f3]is_lemma_type3(lem3) &*& is_lemma_type3(lem3) &*&
               [f4]is_lemma_type4(targ1, targ2, lem4) &*& is_lemma_type4(targ1, targ2, lem4); @*/
{
  //@ duplicate_lemma_function_pointer_chunk(lemma_type1);
  //@ assert [f1]is_lemma_type1(lem1) &*& is_lemma_type1(lem1);
  //@ duplicate_lemma_function_pointer_chunk(lemma_type2);
  //@ assert [f2]is_lemma_type2(lem2) &*& is_lemma_type2(lem2);
  //@ duplicate_lemma_function_pointer_chunk(lemma_type3);
  //@ assert [f3]is_lemma_type3(lem3) &*& is_lemma_type3(lem3);
  //@ duplicate_lemma_function_pointer_chunk(lemma_type4);
  //@ assert [f4]is_lemma_type4(targ1, targ2, lem4) &*& is_lemma_type4(targ1, targ2, lem4);
}

