#include "spouse.h"
#include "stdio.h"
#include "arraylist.h"
//@ #include "ghostlist.h"
#include "io_helper.h"

/*@
predicate_ctor person_ctor(int gid)(struct person* p) =
  p!=0 &*& person(p, ?spouse) &*& spouse == 0 ? ghost_list_member_handle(gid, p) : ghost_list_member_handle(gid, spouse);

lemma void unique_persons(list<void*> ps, int gid, int i, int j)
  requires foreach(ps, person_ctor(gid)) &*& 0 <= i &*& i < length(ps) &*& 0 <= j &*& j < length(ps) &*& i != j;
  ensures foreach(ps, person_ctor(gid)) &*& nth(i, ps) != nth(j, ps);
{
  mem_nth(i, ps);
  mem_nth(j, ps);
  foreach_remove(nth(i, ps), ps);
  assume(mem(nth(j, ps), remove(nth(i, ps), ps))); // todo
  foreach_remove(nth(j, ps), remove(nth(i, ps), ps));
  open person_ctor(gid)(nth(i, ps));
  open person_ctor(gid)(nth(j, ps));
  person_diff(nth(i, ps), nth(j, ps));
  close person_ctor(gid)(nth(i, ps));
  close person_ctor(gid)(nth(j, ps));
  foreach_unremove(nth(j, ps), remove(nth(i, ps), ps));
  foreach_unremove(nth(i, ps), ps);
}

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
@*/

int main() 
  //@ requires true;
  //@ ensures true;
{
  puts("Welcome to the Municipal Registry\n");
  struct arraylist *persons = create_arraylist();
  //@ int gid = create_ghost_list<void*>();
  //@ close foreach(nil, person_ctor(gid));
  while(true)
    /*@ invariant arraylist(persons, ?ps) &*& ghost_list(gid, ps) &*& foreach(ps, person_ctor(gid)); @*/
  {
    puts("Menu:\n");
    puts("  1. Register birth.\n");
    puts("  2. Register marriage.\n");
    puts("  3. Register divorce.\n");
    puts("  4. Register death.\n");
    puts("  5. Exit.\n");
    int choice = read_int();
    if(choice == 1) {
      struct person *p = create_person();
      list_add(persons, p);
      //@ ghost_list_add_last(gid, p);
      //@ close person_ctor(gid)(p);
      //@ close foreach(nil, person_ctor(gid));
      //@ close foreach(cons(p, nil), person_ctor(gid));
      //@ foreach_append(ps, cons(p, nil));
    } else if (choice == 2) {
      puts("Enter the index of the first person.\n");
      int index1 = read_int();
      puts("Enter the index of the second person.\n");
      int index2 = read_int();
      int max = list_length(persons);
      if(0 <= index1 && index1 < max && 0<= index2 && index2 < max && index1 != index2) {
        struct person* p1 = list_get(persons, index1);
        struct person* p2 = list_get(persons, index2);
        //@ mem_nth(index1, ps);
        //@ foreach_remove(p1, ps);
        //@ open person_ctor(gid)(p1);
        struct person* spouse1 = person_get_spouse(p1);
        //@ mem_nth(index2, ps);
        //@ remove_diff_index_mem(ps, index1, index2);
        //@ foreach_remove(p2, remove(p1, ps));
        //@ open person_ctor(gid)(p2);
        struct person* spouse2 = person_get_spouse(p2);
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
      puts("Enter the husband's index.");
      int index = read_int();
      int max = list_length(persons);
      if(0 <= index && index < max) {
        struct person* p = list_get(persons, index);
        //@ mem_nth(index, ps);
        //@ foreach_remove(p, ps);
        //@ open person_ctor(gid)(p);
        struct person *spouse = person_get_spouse(p);
        //@ spouse_diff(p);
        if(spouse != 0) {
          //@ ghost_list_member_handle_lemma();
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
      // todo
    } else if (choice == 5) {
      //@ assume(false);
      return 0;
    } else {
      puts("Invalid Choice");
    }
  }
}


