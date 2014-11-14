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
typedef lemma void lemma_type5<T>(fixpoint(T, int) targ)(T arg);
  requires true;
  ensures  true;

lemma void test1() nonghost_callers_only
  requires [?f]is_lemma_type1(?lem);
  ensures  [f]is_lemma_type1(lem) &*& is_lemma_type1(lem);
{
  duplicate_lemma_function_pointer_chunk(lemma_type1);
  assert [f]is_lemma_type1(lem) &*& is_lemma_type1(lem);
}

lemma void test2() nonghost_callers_only
  requires [?f]is_lemma_type2(?lem);
  ensures  [f]is_lemma_type2(lem) &*& is_lemma_type2(lem);
{
  duplicate_lemma_function_pointer_chunk(lemma_type2);
  assert [f]is_lemma_type2(lem) &*& is_lemma_type2(lem);
}

lemma void test3() nonghost_callers_only
  requires [?f]is_lemma_type3(?lem);
  ensures  [f]is_lemma_type3(lem) &*& is_lemma_type3(lem);
{
  duplicate_lemma_function_pointer_chunk(lemma_type3);
  assert [f]is_lemma_type3(lem) &*& is_lemma_type3(lem);
}

lemma void test4() nonghost_callers_only
  requires [?f]is_lemma_type4(?targ1, ?targ2, ?lem);
  ensures  [f]is_lemma_type4(targ1, targ2, lem) &*& 
           is_lemma_type4(targ1, targ2, lem);
{
  duplicate_lemma_function_pointer_chunk(lemma_type4);
  assert [f]is_lemma_type4(targ1, targ2, lem) &*& 
         is_lemma_type4(targ1, targ2, lem);
}

lemma void test5<T>() nonghost_callers_only
  requires [?f]is_lemma_type5<T>(?targ, ?lem);
  ensures  [f]is_lemma_type5<T>(targ, lem) &*& 
           is_lemma_type5<T>(targ, lem);
{
  duplicate_lemma_function_pointer_chunk(lemma_type5);
  assert [f]is_lemma_type5<T>(targ, lem) &*& 
         is_lemma_type5<T>(targ, lem);
}

@*/

void test_all()
  /*@ requires [?f1]is_lemma_type1(?lem1) &*& 
               [?f2]is_lemma_type2(?lem2) &*& 
               [?f3]is_lemma_type3(?lem3) &*& 
               [?f4]is_lemma_type4(?targ1, ?targ2, ?lem4) &*&
               [?f5]is_lemma_type5(?targ3, ?lem5); @*/
  /*@ ensures  [f1]is_lemma_type1(lem1) &*& is_lemma_type1(lem1) &*& 
               [f2]is_lemma_type2(lem2) &*& is_lemma_type2(lem2) &*& 
               [f3]is_lemma_type3(lem3) &*& is_lemma_type3(lem3) &*&
               [f4]is_lemma_type4(targ1, targ2, lem4) &*& is_lemma_type4(targ1, targ2, lem4) &*&
               [f5]is_lemma_type5(targ3, lem5) &*& is_lemma_type5(targ3, lem5); @*/
{
  //@ duplicate_lemma_function_pointer_chunk(lemma_type1);
  //@ assert [f1]is_lemma_type1(lem1) &*& is_lemma_type1(lem1);
  //@ duplicate_lemma_function_pointer_chunk(lemma_type2);
  //@ assert [f2]is_lemma_type2(lem2) &*& is_lemma_type2(lem2);
  //@ duplicate_lemma_function_pointer_chunk(lemma_type3);
  //@ assert [f3]is_lemma_type3(lem3) &*& is_lemma_type3(lem3);
  //@ duplicate_lemma_function_pointer_chunk(lemma_type4);
  //@ assert [f4]is_lemma_type4(targ1, targ2, lem4) &*& is_lemma_type4(targ1, targ2, lem4);
  //@ duplicate_lemma_function_pointer_chunk(lemma_type5);
  //@ assert [f5]is_lemma_type5(targ3, lem5) &*& is_lemma_type5(targ3, lem5);
}

