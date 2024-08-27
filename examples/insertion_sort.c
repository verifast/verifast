/**
 * This example consists of an insertion sort algorithm for linked lists of integers,
 * verified for memory safety.
 *
 * @date 13 Aug 2014
 * @author Pieter Agten <pieter.agten@cs.kuleuven.be>
 */


struct list_node {
  int value;
  struct list_node* next;
};


/*@
  // Predicate describing a complete linked list
  predicate list_pred(struct list_node* n;) =
    n == 0 ? 
      true
    :
      n->value |-> ?nValue &*& n->next |-> ?next &*& list_pred(next);
@*/

/*@
  // Predicate describing a segment of a linked list from 'start' until 
  // 'end' (not including 'end')
  predicate lseg_pred(struct list_node* start, struct list_node* end;) =
    start == end ?
      true
    :
      start->value |-> ?startValue &*& start->next |-> ?next &*& start != 0 &*& start != next &*& lseg_pred(next, end);
@*/

/*@  
  // Lemma for converting a full list predicate into a list segment predicate
  lemma void list_to_lseg(struct list_node *l)
    requires list_pred(l);
    ensures lseg_pred(l, 0);
  {
    open list_pred(l);
    if (l != 0) {
      list_to_lseg(l->next);
      
      // We need the next two lines to let VeriFast know that l != l->next
      open lseg_pred(l->next, 0);
      close lseg_pred(l->next, 0);
    }
    close lseg_pred(l, 0);
  }
@*/

/*@  
  // Lemma for converting a list segment predicate describing a complete
  // list into a full list predicate.
  lemma void lseg_to_list(struct list_node *n)
    requires lseg_pred(n, 0);
    ensures list_pred(n);
  {
    open lseg_pred(n, 0);
    if (n != 0) {
        lseg_to_list(n->next);
    }
    close list_pred(n);
  }
@*/

/*@  
  // Lemma for adding (appending) a node to a list segment predicate
  lemma void lseg_append_node(struct list_node* lseg_start, struct list_node* lseg_end)
    requires lseg_pred(lseg_start, lseg_end) &*& lseg_end != 0 &*& lseg_end->value |-> ?endValue &*& lseg_end->next |-> ?next1 &*& next1->value |-> ?next1Value &*& next1->next |-> ?next2;
    ensures lseg_pred(lseg_start, next1) &*& next1->value |-> next1Value &*& next1->next |-> next2;
  {
    open lseg_pred(lseg_start, lseg_end);
    if (lseg_start == lseg_end) {
      close lseg_pred(next1, next1);
    } else {
      lseg_append_node(lseg_start->next, lseg_end);
    }
    close lseg_pred(lseg_start, next1);
  }
@*/

/*@  
  // Lemma for concatenating two 'adjacent' list segment predicates, where the latter list segment
  // doesn't describe an entire list
  lemma void lseg_concat(struct list_node *first, struct list_node* n, struct list_node* last)
    requires lseg_pred(first, n) &*& lseg_pred(n, last) &*& last->value |-> ?last_v &*& last->next |-> ?last_next;
    ensures lseg_pred(first, last) &*& last->value |-> last_v &*& last->next |-> last_next;
  {
    open lseg_pred(first, n);
    if (first != n) {
        open lseg_pred(n, last);
        close lseg_pred(n, last);
    
        lseg_concat(first->next, n, last);
        close lseg_pred(first, last);
    }
  }
@*/

/*@  
  // Lemma for concatenating two 'adjacent' list segment predicates, where the latter list segment
  // describes an entire list
  lemma void lseg_concat_full(struct list_node *first)
    requires lseg_pred(first, ?n) &*& lseg_pred(n, 0);
    ensures lseg_pred(first, 0);
  {
    open lseg_pred(first, n);
    if (first != n) {
        open lseg_pred(n, 0);
        close lseg_pred(n, 0);
    
        lseg_concat_full(first->next);
        close lseg_pred(first, 0);
    }
  }
@*/



static int compare(struct list_node* n0, struct list_node* n1)
//@ requires n0->value |-> ?v0 &*& n1->value |-> ?v1;
//@ ensures n0->value |-> v0 &*& n1->value |-> v1 &*& result == (v0 < v1 ? -1 : v0 > v1 ? 1 : 0);
{
  if (n0->value < n1->value) {
    return -1;
  } else if (n0->value > n1->value) {
    return 1;
  } else {
    return 0;
  }
}



void insertion_sort_core(struct list_node** pfirst)
//@ requires *pfirst |-> ?l &*& list_pred(l);
//@ ensures *pfirst |-> ?l0 &*& list_pred(l0);
{
  if (*pfirst == 0) {
    // Empty list is trivially sorted
    return;
  }  
  
  struct list_node* last_sorted = *pfirst;
  while (last_sorted->next != 0)
    /*@ invariant pointer(pfirst, ?first) &*& first != 0 &*& lseg_pred(first, last_sorted) &*& last_sorted->value |-> ?last_sortedValue &*& last_sorted->next |-> ?last_sorted_next &*&
                   last_sorted != 0 &*& list_pred(last_sorted_next);
    @*/
  {
    //@ assert last_sorted->next != 0;
    
    //@ struct list_node* n = *pfirst;
    struct list_node** pn = pfirst;
    //@ open lseg_pred(*pn, last_sorted);
    int comparison = compare(*pn, last_sorted->next); // Cannot inline this call into the while-condition, because of C's unspecified evaluation order in this case
    //@ close lseg_pred(*pn, last_sorted);
    while (pn != &(last_sorted->next) && comparison < 0)
      /*@ invariant 
            pointer(pfirst, first) &*&
                  (pn == pfirst ? 
                    n == first &*&
                    lseg_pred(first, last_sorted) &*&
                    last_sorted->value |-> ?last_sortedValue1 &*& last_sorted->next |-> last_sorted_next &*&
                    list_pred(last_sorted_next)
                  :
                    (pn == &(last_sorted->next) ?
                      lseg_pred(first, last_sorted) &*& last_sorted->value |-> ?last_sortedValue1 &*& last_sorted->next |-> last_sorted_next &*& list_pred(last_sorted_next)
                    :
                      lseg_pred(first, ?prev_n) &*& prev_n != 0 &*& prev_n->value |-> ?prev_nValue &*& pn == &(prev_n->next) &*& pointer(pn, n) &*& lseg_pred(n, last_sorted) &*&
                      n != first &*& last_sorted->value |-> ?last_sortedValue1 &*& last_sorted->next |-> last_sorted_next &*& list_pred(last_sorted_next) &*& n != last_sorted_next
                    )
                  );
      @*/
    { 
      //@ struct list_node** old_pn = pn;
      /*@
      if (pn != &(last_sorted->next)) {
        open lseg_pred(n, last_sorted);
      }
      @*/
      pn = &((*pn)->next);
      //@ struct list_node* old_n = n;
      //@ n = n->next;
      //@ pointer_distinct(pn, pfirst);
      
      
      if (pn != &(last_sorted->next)) {
        /*@
        open lseg_pred(n, _);
        @*/
        comparison = compare(*pn, last_sorted->next);
        /*@
          if (old_pn == pfirst) {
            close lseg_pred(first, first);
          } else {
            // We need to make an lseg_pred(first, n), where n is the node before the new n
            assert lseg_pred(first, ?prev_n);
            close list_node_next(prev_n, old_n);
            lseg_append_node(first, prev_n);
          
            open lseg_pred(first, old_n);
            close lseg_pred(first, old_n);
          }
        @*/
      } else {
        /*@
        if (old_pn != pfirst) {
            // Need to get to an lseg_pred(first, last_sorted)
            close list_node_next(old_n, n);
            assert lseg_pred(first, ?prev_n);
            close list_node_next(prev_n, old_n);
            lseg_append_node(first, prev_n);
        }
        @*/
      }
    }
    
    
    // Found insertion point (right before *pn), so let's move the first unsorted
    // node into the sorted part, right before *pn.
    /*@
    if (pn == &(last_sorted->next)) {
      open list_node_next(last_sorted, last_sorted_next);
    }
    @*/
    if (pn != &(last_sorted->next)) {
      struct list_node* first_unsorted = last_sorted->next;
      //@ open list_pred(last_sorted->next);
      // Remove first unsorted element from list
      last_sorted->next = first_unsorted->next;
      // Insert first unsorted element at right position in list
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      
      /*@
      if (pn != pfirst) {
        // We need to make an lseg_pred(first, last_sorted);
        assert lseg_pred(first, ?prev_n);
        close list_node_next(prev_n, last_sorted_next);
        close lseg_pred(prev_n, last_sorted_next);
        close lseg_pred(last_sorted_next, n);
            
        open list_pred(last_sorted->next); 
        close list_pred(last_sorted->next);

        lseg_concat(last_sorted_next, n, last_sorted);
        lseg_concat(prev_n, last_sorted_next, last_sorted);
        lseg_concat(first, prev_n, last_sorted);
      }
      @*/      
    } else {
      // First unsorted element is already in the correct position
      //@ struct list_node* old_last_sorted = last_sorted;
      last_sorted = last_sorted->next;
      //@ open list_pred(last_sorted_next);
      //@ lseg_append_node(first, old_last_sorted);
      //@ close list_pred(last_sorted_next);
    }
  }
  //@ close list_pred(last_sorted);
  //@ list_to_lseg(last_sorted);
  //@ lseg_concat_full(first);
  //@ lseg_to_list(first);
}


struct list_node* insertion_sort(struct list_node* l)
//@ requires list_pred(l);
//@ ensures list_pred(result);
{
  insertion_sort_core(&l);
  return l;
}

