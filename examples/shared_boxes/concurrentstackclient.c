#include "concurrentstack.h"

/*@
fixpoint bool sublist<t>(list<t> vs1, list<t> vs2) {
  switch(vs1) {
    case nil: return true;
    case cons(h, t): return mem(h, vs2) && sublist(t, vs2);
  }
}

box_class incr_box(list<void*> all, list<void*> vs) {
  invariant distinct(all) && distinct(vs) && sublist(vs, all) == true;
  
  action push(void* x);
    requires ! mem(x, all);
    ensures vs == cons(x, old_vs) && all == cons(x, old_all);
    
  action pop();
    requires true;
    ensures vs == tail(old_vs) && all == old_all;
    
  handle_predicate not_contains(bool popped, void* x) {
    invariant ! popped || (mem(x, all) && ! mem(x, vs));
    
    preserved_by push(y) {
    }
    preserved_by pop() {
      assert vs == tail(old_vs);
      switch(old_vs) {
        case nil:
        case cons(h, t):
      }
    }
  }
}
@*/

//@ predicate_ctor myi(box id)(list<void*> vs) = incr_box(id, ?all, vs);

void consumer(struct stack* s, struct stack_client* client) 
  //@ requires exists<box>(?id) &*& stack_client(s, ?f, myi(id), client);
  //@ ensures false;
{
  {
  /*@
    predicate_family_instance stack_pop_pre(my_pop_lemma)() = true;
    predicate_family_instance stack_pop_post(my_pop_lemma)(bool success, void* res) = not_contains(?ha, id, success, res);
    lemma void my_pop_lemma()
      requires stack_pop_pre(my_pop_lemma)() &*& myi(id)(?vs);
      ensures stack_pop_post(my_pop_lemma)(vs != nil, ?out) &*& (vs == nil ? myi(id)(nil) : myi(id)(tail(vs)) &*& out == head(vs));
    {
      open stack_pop_pre(my_pop_lemma)();
      open myi(id)(vs);
      switch(vs) {
        case nil:
        case cons(h,t):
      }
      assert incr_box(id, ?all, vs);
      handle ha = create_handle incr_box_handle(id);
      consuming_box_predicate incr_box(id, all, vs)
      consuming_handle_predicate incr_box_handle(ha)
      perform_action pop()
      {
        
      } 
      producing_box_predicate incr_box(all, tail(vs))
      producing_handle_predicate not_contains(ha, vs != nil, vs == nil ? (void*)0 : head(vs));
      close myi(id)(tail(vs));
      close stack_pop_post(my_pop_lemma)(vs != nil, vs == nil ? (void*)0 : head(vs));
    }
    
  @*/ 
   //@ produce_lemma_function_pointer_chunk(my_pop_lemma) : stack_pop_lemma(myi(id))() { call();};
  //@ close stack_pop_pre(my_pop_lemma)();
    void* x1, x2;
    bool success = stack_pop(s, client, &x1);
    void* y = x1;
    if(! success) consumer(s, client);
    //@ open stack_pop_post(my_pop_lemma)(_, _);
    {
    /*@
    predicate_family_instance stack_pop_pre(my_pop_lemma2)() = not_contains(?ha, id, true, y);
    predicate_family_instance stack_pop_post(my_pop_lemma2)(bool success2, void* res) = ! success2 || res != y;
    lemma void my_pop_lemma2()
      requires stack_pop_pre(my_pop_lemma2)() &*& myi(id)(?vs);
      ensures stack_pop_post(my_pop_lemma2)(vs != nil, ?out) &*& (vs == nil ? myi(id)(nil) : myi(id)(tail(vs)) &*& out == head(vs));
    {
      open stack_pop_pre(my_pop_lemma2)();
      open myi(id)(vs);
      switch(vs) {
        case nil:
        case cons(h,t):
      }
      assert incr_box(id, ?all, vs);
      assert not_contains(?ha, _, _, _);
      consuming_box_predicate incr_box(id, all, vs)
      consuming_handle_predicate not_contains(ha, true, y)
      perform_action pop()
      {
        
      } 
      producing_box_predicate incr_box(all, tail(vs))
      producing_handle_predicate not_contains(ha, vs != nil, vs == nil ? (void*)0 : head(vs));
      close myi(id)(tail(vs));
      close stack_pop_post(my_pop_lemma2)(vs != nil, vs == nil ? (void*)0 : head(vs));
      leak not_contains(_, _, _, _);
    }
    
    @*/ 
    //@ produce_lemma_function_pointer_chunk(my_pop_lemma2) : stack_pop_lemma(myi(id))() { call();};
    //@ close stack_pop_pre(my_pop_lemma2)();
    success = stack_pop(s, client, &x2);
    if(! success) consumer(s, client);
    //@ open stack_pop_post(my_pop_lemma2)(true, x2); 
    assert x1 != x2;
    }
    consumer(s, client);
  }
} 

int main() 
  //@ requires true;
  //@ ensures true;
{
  return 0;
}
