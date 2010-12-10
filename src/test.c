struct list
{
  struct list* next;
  int field;
};

/*@

predicate Node(struct list* P, struct list* Q) =
  malloc_block_list(P) &*&
  P->next |-> Q &*&
  P->field |-> ?field;

predicate LSeg(struct list* P, struct list* Q) =
  P == Q ? emp
         : Node(P, ?R) &*&
           LSeg(R, Q);
           
@*/

void scan(struct list* lst)
  //@ requires LSeg(lst, 0);
  //@ ensures LSeg(lst, 0);
{
  struct list* p = lst;
  
  while ( p != 0 )
    //@ invariant emp;
  {
    p = p->next;
  }
}

struct list* reverse(struct list* c)
  //@ requires LSeg(c, 0);
  //@ ensures LSeg(c, 0);
{
  struct list* p = 0;
  
  while ( c != 0 )
    //@ invariant emp;
  {
    struct list* n = c->next;
    c->next = p;
    p = c;
    c = c->next;    
  }
  
  return p;
}

void destroy(struct list* lst)
  //@ requires LSeg(lst, 0);
  //@ ensures emp;
{
  while ( lst != 0 )
    //@ invariant lst == 0 ? emp : LSeg(?next, 0);
  {    
    struct list* next = lst->next;
    free(lst);
    lst = next;
  }
}

struct list* create_singleton()
  //@ requires emp;
  //@ ensures emp;
{
  struct list* xs = malloc( sizeof( struct list ) );
  return xs;
}

struct list* copy(struct list* lst)
  //@ requires LSeg(lst, 0);
  //@ ensures emp;
{
  struct list* xs = lst;
  struct list* ys = 0;
  struct list* r = 0;
  
  while ( xs != 0 )
    //@ invariant emp;
  {
    struct list* temp = malloc( sizeof( struct list ) );
    
    if ( ys != 0 )
    {
      ys->next = temp;
    }
    else
    {
      r = temp;
    }
    
    xs = xs->next;
    ys = temp;
    ys->next = 0;
  }
  
  return r;
}
