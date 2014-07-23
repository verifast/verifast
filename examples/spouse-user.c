#include "spouse.h"
#include "stdio.h"
#include "arraylist.h"
//@ #include "ghostlist.gh"
#include "io_helper.h"
#include <stdbool.h>

/*@
predicate_ctor person_ctor(int gid)(struct person* p) =
  p!=0 &*& person(p, ?spouse) &*& spouse == 0 ? ghost_list_member_handle(gid, p) : ghost_list_member_handle(gid, spouse);

lemma void remove_diff_mem<t>(list<t> xs, t x, t y)
  requires mem(x, xs) == true &*& mem(y, xs) == true &*& x != y;
  ensures mem(y, remove(x, xs)) == true;
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      if(h == x) {

      } else {
        if(h == y) {
        } else {
          remove_diff_mem(t, x, y);
        }
      }     
  }
}

lemma void remove_diff_index_mem<t>(list<t> xs, int i, int j);
  requires mem(nth(i, xs), xs) == true &*& mem(nth(j, xs), xs) == true &*& i != j;
  ensures mem(nth(j, xs), remove(nth(i, xs), xs)) == true;
  
lemma void foreach_remove_nth<t>(int n, list<t> xs);
    requires foreach(xs, ?p) &*& 0 <= n &*& n < length(xs);
    ensures foreach(remove_nth(n, xs), p) &*& p(nth(n, xs));
    
 
lemma void remove_nth_mem<t>(list<t> xs, int n, t x) 
  requires 0 <= n &*& n < length(xs) &*& mem(x, xs) == true &*& nth(n, xs) != x;
  ensures mem(x, remove_nth(n, xs)) == true;
{
  switch(xs) {
    case nil: 
    case cons(h, t): 
      if(h == x) {
      } else {
        if(n == 0) {
        } else {
          remove_nth_mem(t, n - 1, x);
        }
      }
  }
}
@*/

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct arraylist *persons = create_arraylist();
  puts("Welcome to the Municipal Registry\n");
  //@ int gid = create_ghost_list<void*>();
  //@ close foreach(nil, person_ctor(gid));
  while(true)
    /*@ invariant arraylist(persons, ?ps) &*& ghost_list(gid, ps) &*& foreach(ps, person_ctor(gid)); @*/
  {
    int choice = 0;
    puts("Menu:\n");
    puts("  1. Register birth.\n");
    puts("  2. Register marriage.\n");
    puts("  3. Register divorce.\n");
    puts("  4. Register death.\n");
    puts("  5. Exit.\n");
    choice = read_int();
    if(choice == 1) {
      struct person *p = create_person();
      list_add(persons, p);
      //@ ghost_list_add_last(gid, p);
      //@ close person_ctor(gid)(p);
      //@ close foreach(nil, person_ctor(gid));
      //@ close foreach(cons(p, nil), person_ctor(gid));
      //@ foreach_append(ps, cons(p, nil));
    } else if (choice == 2) {
      int index1 = 0; int index2 = 0; int max = 0; struct person* p1 = 0; struct person* p2 = 0; struct person* spouse1 = 0; struct person* spouse2 = 0;
      puts("Enter the index of the first person.\n");
      index1 = read_int();
      puts("Enter the index of the second person.\n");
      index2 = read_int();
      max = list_length(persons);
      if(0 <= index1 && index1 < max && 0<= index2 && index2 < max && index1 != index2) {
        p1 = list_get(persons, index1);
        p2 = list_get(persons, index2);
        //@ foreach_remove(p1, ps);
        //@ open person_ctor(gid)(p1);
        spouse1 = person_get_spouse(p1);
        //@ remove_diff_index_mem(ps, index1, index2);
        //@ foreach_remove(p2, remove(p1, ps));
        //@ open person_ctor(gid)(p2);
        spouse2 = person_get_spouse(p2);
        if(spouse1 == 0 && spouse2 == 0) {
          marry(p1, p2);
          //@ close person_ctor(gid)(p1);
          //@ close person_ctor(gid)(p2);
          //@ foreach_unremove(p2, remove(p1, ps));
          //@ foreach_unremove(p1, ps);
        } else {
          //@ close person_ctor(gid)(p1);
          //@ close person_ctor(gid)(p2);
          //@ foreach_unremove(p2, remove(p1, ps));
          //@ foreach_unremove(p1, ps);
          puts("One of the persons is already married.");
        }
      } else {
        puts("Index out of bounds or same index.");
      }
    } else if (choice == 3) {
      int index = 0; int max = 0; struct person *p = 0; struct person *spouse = 0;
      puts("Enter the husband's index.");
      index = read_int();
      max = list_length(persons);
      if(0 <= index && index < max) {
        p = list_get(persons, index);
        //@ foreach_remove(p, ps);
        //@ open person_ctor(gid)(p);
        spouse = person_get_spouse(p);
        //@ spouse_diff(p);
        if(spouse != 0) {
          //@ assert ghost_list_member_handle(?id, ?d);
          //@ ghost_list_member_handle_lemma(id, d);
          //@ remove_diff_mem(ps, p, spouse);
          //@ foreach_remove(spouse, remove(p, ps));
          //@ open person_ctor(gid)(spouse);
          //@ married_lemma(p);
          divorce(p);
          //@ close person_ctor(gid)(p);
          //@ close person_ctor(gid)(spouse);
          //@ foreach_unremove(spouse, remove(p, ps));
          //@ foreach_unremove(p, ps);
        } else {
          puts("The person is not married.");
          //@ close person_ctor(gid)(p);
          //@ foreach_unremove(p, ps);
        }
      } else {
        puts("Invalid index");
      }
    } else if (choice == 4) {
      int index = 0; int max = 0; struct person *p = 0; struct person *spouse = 0;
      puts("Enter a person's index.");
      index = read_int();
      max = list_length(persons);
      if(0 <= index && index < max) {
        p = list_get(persons, index);
        list_remove_nth(persons, index);
        //@ foreach_remove_nth(index, ps);
        //@ open person_ctor(gid)(nth(index, ps));
        spouse = person_get_spouse(p);
        //@ spouse_diff(p);
        if(spouse != 0) {
          //@ assert ghost_list_member_handle(?id, ?d);
          //@ ghost_list_member_handle_lemma(id, d);
          //@ remove_nth_mem(ps, index, spouse);
          //@ foreach_remove(spouse, remove_nth(index, ps));
          //@ open person_ctor(gid)(spouse);
          //@ married_lemma(p);
        }
        //@ ghost_list_remove_nth(gid, index);
        die(p);
        if(spouse != 0) {
          //@ close person_ctor(gid)(spouse);
          //@ foreach_unremove(spouse, remove_nth(index, ps));
        }
      } else {
        puts("Invalid index.");
      }
    } else if (choice == 5) {
      int i = list_length(persons);
      while(i != 0) 
        //@ invariant arraylist(persons, ?ps0) &*& ghost_list(gid, ps0) &*& foreach(ps0, person_ctor(gid)) &*& i == length(ps0);
      {
        struct person* p = list_get(persons, 0);
        struct person* spouse = 0;
        list_remove_nth(persons, 0);
        //@ foreach_remove_nth(0, ps0);
        //@ open person_ctor(gid)(p);
        //@ spouse_diff(p);
        spouse = person_get_spouse(p);
        //@ assume(spouse == 0); // todo
        //@ ghost_list_remove_nth(gid, 0);
        die(p);
        i = list_length(persons);
      }
      //@ switch(ps0) { case nil: case cons(h0, t0): }
      //@ ghost_list_dispose();
      //@ open foreach(nil, _);
      list_dispose(persons);
      return 0;
    } else {
      puts("Invalid Choice");
    }
  }
}


