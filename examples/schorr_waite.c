#include "stdlib.h"

struct node {
  bool m; // marked
  bool c; // which child is explored
  struct node* l;
  struct node* r;
  
};

/*@
predicate tree(struct node* t, bool marked) = 
  t==0 ? true : t->m |-> marked &*& t->c |-> ?c &*& t->l |-> ?l &*& t->r |-> ?r &*& tree(l, marked) &*& tree(r, marked);
  
predicate stack(struct node* t) =
  t == 0 ? true : t->m |-> true &*& t->c |-> ?c &*& t->l |-> ?l &*& t->r |-> ?r &*& (c == false ? stack(l) &*& tree(r, false) : stack(r) &*& tree(l, true));

@*/

void schorr_waite(struct node* root) 
  //@ requires tree(root, false);
  //@ ensures tree(_, true);
{
  struct node* t = root; 
  struct node* p = 0;
  bool tm = false;
  if(t!=0) {
    //@ open tree(t, false);
    tm = t->m;
    //@ close tree(t, false);
  }
  //@ close stack(p);
  while(p != 0 || (t != 0 && ! tm))
    //@ invariant tree(t, tm) &*& stack(p);
  {
    if(t == 0 || tm) {
      //@ open stack(p);
      if(p->c) { // pop
        struct node* q = t;
        t = p;
        p = p->r;
        t->r = q;
        if(t != 0) { tm = t->m; } 
        if(q == 0) 
        { 
          //@ open tree(q, _);
          //@ close tree(q, true);
        }
        //@ close tree(t, true);
      } else { // swing
        struct node* q = t;
        t = p->r;
        p->r = p->l;
        p->l = q;
        p->c = true;
        if(q == 0) {
          //@ open tree(q, _);
          //@ close tree(q, true);
        }
        //@ close stack(p);
        //@ open tree(t, false);
        if(t != 0) { tm = t->m; } else { tm = false; /* hack */ }
        //@ close tree(t, false); 
      }
    } else { // push
      struct node* q = p;
      //@ open tree(t, false);
      p = t;
      t = t->l;
      p->l = q;
      p->m = true;
      p->c = false;
      //@ open tree(t, _);
      if(t != 0) { tm = t->m; } else { tm = false; /* hack */ }
      //@ close tree(t, tm);
      //@ close stack(p);
    }
  }
  //@ open stack(p);
  if(t == 0) { 
    //@ open tree(t, _);
    //@ close tree(t, true);
  }
}