//@ #include "assoclist.gh"

/*@
lemma_auto(length(keys(map))) void length_keys<t1, t2>(list<pair<t1, t2> > map)
  requires true;
  ensures length(keys(map)) == length(map);
{
  switch(map) {
    case nil:
    case cons(h, t): length_keys(t);
  }
}

lemma_auto(length(values(map))) void length_values<t1, t2>(list<pair<t1, t2> > map)
  requires true;
  ensures length(values(map)) == length(map);
{
  switch(map) {
    case nil:
    case cons(h, t): length_values(t);
  }
}

lemma_auto void take_values<t1, t2>(int i, list<pair<t1, t2> > map)
  requires 0 <= i && i <= length(map);
  ensures take(i, values(map)) == values(take(i, map));
{
  switch(map) {
    case nil:
    case cons(h, t):
      if(i != 0) take_values(i - 1, t);
  }
}

lemma void take_update_entry<t1, t2>(t1 key, fixpoint(t2, t2) f, list<pair<t1, t2> > map, int i)
  requires 0 <=i &*& i <= length(map);
  ensures update_entry(key, f, take(i, map)) == take(i, update_entry(key, f, map));
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          if(key0 == key) {
          } else {
            if(i == 0) {
            } else {
              take_update_entry(key, f, t, i - 1);
            }
      }
    }
  }
}

lemma_auto(assoc(key, update_entry(key, f, map))) void assoc_update_entry<t1, t2>(t1 key, fixpoint(t2, t2) f, list<pair<t1, t2> > map)
  requires mem(key, keys(map)) == true;
  ensures assoc(key, update_entry(key, f, map)) == f(assoc(key, map));
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
         if(key != key0) {
           assoc_update_entry(key, f, t);
         } 
      };
  }
}

lemma_auto(keys(update_entry(key, f, map))) void update_entry_preserves_keys<t1, t2>(t1 key, fixpoint(t2, t2) f, list<pair<t1, t2> > map) 
  requires true;
  ensures keys(update_entry(key, f, map)) == keys(map);
{
  switch(map) {
    case nil:
    case cons(h, t): switch(h) {
        case pair(key0, value0):
          if(key != key0) update_entry_preserves_keys(key, f, t);
         
      };
  }
}

lemma_auto(append(map1, update_entry(key, f, map2))) void append_update_entry<t1, t2>(t1 key, fixpoint(t2, t2) f, list<pair<t1, t2> > map1, list<pair<t1, t2> > map2) 
  requires ! mem(key, keys(map1));
  ensures append(map1, update_entry(key, f, map2)) == update_entry(key, f, append(map1, map2));
{
  switch(map1) {
    case nil:
    case cons(h, t): switch(h) {
        case pair(key0, value0):
          append_update_entry(key, f, t, map2);
         
      };
  }
}

lemma_auto(assoc(otherkey, update_entry(key, f, map))) void update_entry_preserves_other_values<t1, t2>(t1 otherkey, t1 key, fixpoint(t2, t2) f, list<pair<t1, t2> > map) 
  requires key != otherkey;
  ensures assoc(otherkey, update_entry(key, f, map)) == assoc(otherkey, map);
{
  switch(map) {
    case nil:
    case cons(h, t): switch(h) {
        case pair(key0, value0):
          if(key != key0) update_entry_preserves_other_values(otherkey, key, f, t);
         
      };
  }
}

lemma_auto(mem(pair(key, value), map)) void mem_keys<t1, t2>(t1 key, t2 value, list<pair<t1, t2> > map)
  requires mem(pair(key, value), map) == true;
  ensures mem(key, keys(map)) == true;
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          if(key == key0 && value == value0) {
          } else {
            mem_keys(key, value, t);
          }
      }
  }
}

lemma_auto(mem(pair(key, value), map)) void mem_values<t1, t2>(t1 key, t2 value, list<pair<t1, t2> > map)
  requires mem(pair(key, value), map) == true;
  ensures mem(value, values(map)) == true;
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          if(key == key0 && value == value0) {
          } else {
            mem_values(key, value, t);
          }
      }
  }
}

lemma_auto(keys(update_entry(key, f, map))) void keys_update_entry<t1, t2>(t1 key, fixpoint(t2, t2) f, list<pair<t1, t2> > map)
  requires true;
  ensures keys(update_entry(key, f, map)) == keys(map);
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          if(key == key0) {
          } else {
            keys_update_entry(key, f, t);
          }
      }
  }
}

lemma_auto(length(update_entry(key, f, map))) void length_update_entry<t1, t2>(t1 key, fixpoint(t2, t2) f, list<pair<t1, t2> > map)
  requires true;
  ensures length(update_entry(key, f, map)) == length(map);
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          if(key == key0) {
          } else {
            length_update_entry(key, f, t);
          }
      }
  }
}
  
lemma void distinct_keys_implies_distinct_entries<t1, t2>(list<pair<t1, t2> > map)
  requires distinct(keys(map)) == true;
  ensures distinct(map) == true;
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          distinct_keys_implies_distinct_entries(t);
      }
  }
}

lemma void distinct_values_implies_distinct_entries<t1, t2>(list<pair<t1, t2> > map)
  requires distinct(values(map)) == true;
  ensures distinct(map) == true;
{
  switch(map) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          distinct_values_implies_distinct_entries(t);
      }
  }
}

lemma void append_values<t1, t2>(list<pair<t1, t2> > map1, list<pair<t1, t2> > map2)
  requires true;
  ensures values(append(map1, map2)) == append(values(map1), values(map2));
{
  switch(map1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          append_values(t, map2);
      }
  }
}

lemma void assoc_append<t1, t2>(t1 key, list<pair<t1, t2> > map1,  list<pair<t1, t2> > map2)
  requires !mem(key, keys(map1));
  ensures assoc(key, append(map1, map2)) == assoc(key, map2);
{
  switch(map1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          if(key == key0) {
          } else {
            assoc_append(key, t, map2);
          }
      }
  }
}
  
lemma void assoc_append_l<t1, t2>(t1 key, list<pair<t1, t2> > map1,  list<pair<t1, t2> > map2)
  requires mem(key, keys(map1)) == true;
  ensures assoc(key, append(map1, map2)) == assoc(key, map1);
{
  switch(map1) {
    case nil:
    case cons(h, t):
      switch(h) {
        case pair(key0, value0):
          if(key == key0) {
          } else {
            assoc_append_l(key, t, map2);
          }
      }
  }
}

lemma_auto void keys_remove_assoc<t1, t2>(t1 key, list<pair<t1, t2> > map) 
  requires true;
  ensures keys(remove_assoc(key, map)) == remove(key, keys(map));
{
  switch(map) {
    case nil: 
    case cons(h, t): switch(h) { case pair(k, v): if(k!=key) keys_remove_assoc(key, t); }
  }
}

lemma void remove_assoc_preserves_other_entries<t1, t2>(t1 key, t1 removed, list<pair<t1, t2> > map) 
  requires mem(key, keys(map)) == true && key != removed;
  ensures mem(key, keys(remove_assoc(removed, map))) == true &*& assoc(key, remove_assoc(removed, map)) == assoc(key, map);
{
  switch(map) {
    case nil: 
    case cons(h, t): switch(h) { case pair(k, v): if(k!=removed && k != key) remove_assoc_preserves_other_entries(key, removed, t); }
  }
}

lemma_auto void length_remove_assoc<t1, t2>(t1 key, list<pair<t1, t2> > map)
  requires true;
  ensures length(remove_assoc(key, map)) == (mem(key, keys(map)) ? length(map) - 1 : length(map));
{
  switch(map) {
    case nil: 
    case cons(h, t): switch(h) { case pair(k, v): if( k != key) length_remove_assoc(key, t); }
  }
}
@*/
