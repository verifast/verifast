#ifndef CONCURRENTSTACK_H
#define CONCURRENTSTACK_H

struct stack;
struct stack_client;

//@ predicate stack_client(struct stack* s, real f, predicate(list<void*>) I, struct stack_client* client);
//@ predicate stack(struct stack* s, predicate(list<void*>) I);

struct stack* create_stack();
  //@ requires exists<predicate(list<void*>)>(?I) &*& I(nil);
  //@ ensures result == 0 ? I(nil) : stack(result, I);

struct stack_client* create_client(struct stack* s);
  //@ requires [?f]stack(s, ?I);
  //@ ensures [?g]stack(s, I) &*& result == 0 ? f == g : stack_client(s, ?h, I, result) &*& f == g + h;

void deactivate_client(struct stack* s, struct stack_client* client);
  //@ requires stack_client(s, ?f, ?I, client);
  //@ ensures [f]stack(s, I);
  
/*@
predicate_family stack_push_pre(void* index)();
predicate_family stack_push_post(void* index)();

typedef lemma void stack_push_lemma(predicate(list<void*> vs) I, void* data)();
  requires stack_push_pre(this)() &*& I(?vs);
  ensures stack_push_post(this)() &*& I(cons(data, vs));
@*/

void stack_push(struct stack* s, struct stack_client* client, void* data);
  //@ requires stack_client(s, ?f, ?I, client) &*& is_stack_push_lemma(?lem, I, data) &*& stack_push_pre(lem)();
  //@ ensures stack_client(s, f, I, client) &*& stack_push_post(lem)();
  
/*@
predicate_family stack_pop_pre(void* index)();
predicate_family stack_pop_post(void* index)(bool success, void* res);

typedef lemma void stack_pop_lemma(predicate(list<void*> vs) I)();
  requires stack_pop_pre(this)() &*& I(?vs);
  ensures stack_pop_post(this)(vs != nil, ?out) &*& (vs == nil ? I(nil) : I(tail(vs)) &*& out == head(vs));
@*/

bool stack_pop(struct stack* s, struct stack_client* client, void** out);
  //@ requires stack_client(s, ?f, ?I, client) &*& *out |-> _ &*& is_stack_pop_lemma(?lem, I) &*& stack_pop_pre(lem)();
  //@ ensures stack_client(s, f, I, client) &*& stack_pop_post(lem)(result, ?pst) &*& result ? *out |-> pst : *out |-> _;

void stack_dipose(struct stack* s);
  //@ requires stack(s, ?I);
  //@ ensures I(?vs);

#endif
