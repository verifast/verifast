/*

Full functional correctness proof of doubly-linked list reversal
Stephan van Staden, 2009

*/


typedef struct node {
	int item;
	struct node *next;
	struct node *prev;
} *node;

/*@

predicate node(node no, int i, node ne, node pr)
    = no->item |-> i &*& no->next |-> ne &*& no->prev |-> pr;
    
@*/

typedef struct dllist {
	node head;
	node tail;
} *dllist;

/*@

inductive intlist = | inil | icons(int, intlist);

inductive nodeptrlist = | nnil | ncons(node , nodeptrlist);

predicate linked(node l2, nodeptrlist lambda1, nodeptrlist lambda2, node l3)
    = lambda1 == nnil ? l2 == l3 &*& lambda2 == nnil
                      : linked(l2, ?lambda1p, ?lambda2p, ?l) &*& lambda2 == ncons(l3, lambda2p) &*& lambda1 == ncons(l, lambda1p);

predicate list(node l1, intlist alpha, nodeptrlist lambda1, nodeptrlist lambda2)
    = l1 == 0 ? alpha == inil &*& lambda1 == nnil &*& lambda2 == nnil
                 : node(l1, ?i, ?n, ?p) &*& list(n, ?alphap, ?lambda1p, ?lambda2p) &*& alpha == icons(i, alphap) &*& lambda1 == ncons(l1, lambda1p) &*& lambda2 == ncons(p, lambda2p); 

predicate dll(dllist d, intlist alpha)
    = d->head |-> ?l1 &*& d->tail |-> ?l2 &*& list(l1,alpha,?lambda1,?lambda2) &*& linked(l2,lambda1,lambda2,0);

@*/

/*@

fixpoint intlist app(intlist l1, intlist l2) {
  switch (l1) {
    case inil: return l2;
    case icons(x, v): return icons(x, app(v, l2));
  }
}

fixpoint intlist rev(intlist l) {
  switch (l) {
    case inil: return inil;
    case icons(x, v): return app(rev(v), icons(x, inil));
  }
}

lemma void app_assoc(intlist l1, intlist l2, intlist l3)
  requires emp;
  ensures app(app(l1, l2), l3) == app(l1, app(l2, l3));
{
  switch (l1) {
    case inil:
    case icons(x, v):
      app_assoc(v, l2, l3);
  }
}

lemma void rev_lemma(int i, intlist gamma, intlist alphap)
  requires emp;
  ensures app(rev(icons(i, gamma)), alphap) == app(rev(gamma), icons(i, alphap));
{
  app_assoc(rev(gamma), icons(i, inil), alphap);
}

lemma void app_to_nil(intlist l)
  requires emp;
  ensures app(l, inil) == l;
{
  switch (l) {
    case inil:
    case icons(x, v):
      app_to_nil(v);
  }
}

lemma void rev_app(intlist l1, intlist l2)
  requires emp;
  ensures rev(app(l1, l2)) == app(rev(l2), rev(l1));
{
  switch (l1) {
    case inil:
      app_to_nil(rev(l2));
    case icons(x, v):
      rev_app(v, l2);
      app_assoc(rev(l2), rev(v), icons(x, inil));
  }
}

lemma void rev_twice(intlist l)
  requires emp;
  ensures rev(rev(l)) == l;
{
  switch (l) {
    case inil:
    case icons(x, v):
      rev_app(rev(v), icons(x, inil));
      rev_twice(v);
  }
}

@*/

void reverse(dllist arg)
	//@ requires dll(arg, ?alpha);
 	//@ ensures dll(arg, rev(alpha));
{
	//@ open dll(arg, alpha);
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;
	//@ close list(0, inil, nnil, nnil);
	//@ close linked(ptr, nnil, nnil, ptr);
	while (ptr != 0)
		//@ invariant list(ptr, ?beta, ?lambda1, ?lambda2) &*& arg->tail |-> ?l &*& linked(l, lambda1, lambda2, ?lp) &*& list(lp, ?gamma, ?lambda3, ?lambda4) &*& arg->head |-> ?f &*& linked(f, lambda3, lambda4, ptr) &*& alpha == app(rev(gamma), beta);
	{
		//@ open list(ptr, beta, lambda1, lambda2);
		//@ open linked(l, lambda1, lambda2, lp);
		//@ open node(ptr, ?i, ?n, ?p);
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;
		//@ close node(ptr, i, p, n);
		//@ close list(ptr, icons(i, gamma), ncons(ptr, lambda3), ncons(temp1, lambda4));
		//@ close linked(f, ncons(ptr, lambda3), ncons(temp1, lambda4), temp1);
		ptr = temp1;
        // The following two lines bind the tail of beta to variable betap.
		//@ open list(temp1, ?betap, ?t1, ?t2);
		//@ close list(temp1, betap, t1, t2);
		//@ rev_lemma(i, gamma, betap);
	}
	//@ open list(ptr, beta, lambda1, lambda2);
	//@ open linked(l, lambda1, lambda2, lp);
	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
	//@ app_to_nil(rev(gamma));
	//@ rev_twice(gamma);
	//@ close dll(arg, rev(alpha));
}
