import java.util.*;

/*@

lemma_auto void length_append_auto<t>(list<t> xs, list<t> ys)
    requires true;
    ensures length(append(xs, ys)) == length(xs) + length(ys);
{
    length_append(xs, ys);
}

lemma_auto(length(drop(n, xs))) void length_drop_auto<t>(int n, list<t> xs)
    requires 0 <= n && n <= length(xs);
    ensures length(drop(n, xs)) == length(xs) - n;
{
    length_drop(n, xs);
}

lemma_auto void drop_drop_auto<t>(int m, int n, list<t> xs)
    requires 0 <= m && 0 <= n && m + n <= length(xs);
    ensures drop(m, drop(n, xs)) == drop(m + n, xs);
{
    drop_drop(m, n, xs);
}

fixpoint boolean descendingFrom(int x0, list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x1, xs1): return x0 > x1 && x1 >= 0 && descendingFrom(x1, xs1);
    }
}

lemma_auto void length_remove_nth<t>(int n, list<t> xs)
    requires 0 <= n && n < length(xs);
    ensures length(remove_nth(n, xs)) == length(xs) - 1;
{
    switch (xs) {
        case nil:
        case cons(x0, xs0):
            if (n == 0) {
            } else {
                length_remove_nth(n - 1, xs0);
            }
    }
}

lemma void length_remove_nths(list<int> rs, list<Object> es)
    requires descendingFrom(length(es), rs) == true;
    ensures length(remove_nths(rs, es)) == length(es) - length(rs);
{
    switch (rs) {
        case nil:
        case cons(r, rs1):
            length_remove_nth(r, es);
            switch (rs1) { case nil: case cons(r1, rs2): }
            length_remove_nths(rs1, remove_nth(r, es));
    }
}

lemma void nth_remove_nth<t>(int i, int n, list<t> es)
    requires 0 <= n &*& n < i &*& i < length(es);
    ensures nth(i, es) == nth(i - 1, remove_nth(n, es));
{
    switch (es) {
        case nil:
        case cons(e, es0):
            if (n == 0) {
            } else {
                nth_remove_nth(i - 1, n - 1, es0);
            }
    }
}

lemma_auto void nth_remove_nth_0<t>(int i, int n, list<t> es)
    requires 0 <= n && n < length(es) && 0 <= i && i + 1 < length(es);
    ensures nth(i, remove_nth(n, es)) == (i < n ? nth(i, es) : nth(i + 1, es));
{
    switch (es) {
        case nil:
        case cons(e, es0):
            if (i == 0) {
            } else if (n == 0) {
            } else {
                nth_remove_nth_0(i - 1, n - 1, es0);
            }
    }
}

lemma void nth_remove_nths(int i, list<int> rs, list<Object> es)
    requires length(es) > i &*& descendingFrom(i, rs) == true;
    ensures nth(i, es) == nth(i - length(rs), remove_nths(rs, es));
{
    switch (rs) {
        case nil:
        case cons(r, rs1):
            nth_remove_nth(i, r, es);
            length_remove_nth(r, es);
            switch (rs1) { case nil: case cons(r1, rs2): }
            nth_remove_nths(i - 1, rs1, remove_nth(r, es));
    }
}

lemma void remove_nth_remove_nth<t>(int i, int n, list<t> es)
    requires 0 <= n &*& n < i &*& i < length(es);
    ensures remove_nth(n, remove_nth(i, es)) == remove_nth(i - 1, remove_nth(n, es));
{
    switch (es) {
        case nil:
        case cons(e0, es0):
            if (n == 0) {
            } else {
                remove_nth_remove_nth(i - 1, n - 1, es0);
            }
    }
}

lemma void remove_nth_remove_nths(int i, list<int> rs, list<Object> es)
    requires length(es) > i &*& descendingFrom(i, rs) == true;
    ensures remove_nths(cons(i, rs), es) == remove_nth(i - length(rs), remove_nths(rs, es));
{
    switch (rs) {
        case nil:
        case cons(r0, rs0):
            length_remove_nth(r0, es);
            switch (rs0) { case nil: case cons(r1, rs1): }
            remove_nth_remove_nths(i - 1, rs0, remove_nth(r0, es));
            remove_nth_remove_nth(i, r0, es);
    }
}

@*/
    
final class ArrayListIterator<T> implements Iterator<T> {
    
    ArrayList<T> list;
    //@ real frac;
    //@ list<Object> oldElements;
    //@ list<int> removals;
    //@ int nextRemoveIndex;
    //@ boolean hasCurrentElement;
    int index;
    
    /*@
    
    predicate Iterator(fixpoint(int, option<Object>) elements, option<int> currentIndex, int nextIndex) =
        [_]list |-> ?l &*& [_]frac |-> ?f &*& [f]l.List(?es) &*&
        [_]oldElements |-> ?oes &*& [1/2]removals |-> ?rs &*&
        elements == (seq_of_list)(oes) &*&
        es == remove_nths(rs, oes) &*&
        index |-> ?i &*& 0 <= i &*& i <= length(es) &*&
        hasCurrentElement |-> ?hce &*&
        nextIndex == i + length(rs) &*& nextIndex <= length(oes) &*&
        nextRemoveIndex |-> ?nri &*&
        currentIndex == (hce ? some(nri) : none) &*&
        (hce ? nextIndex == nri + 1 &*& length(rs) <= nri : nextIndex == nri) &*&
        f == 1 || rs == nil &*&
        descendingFrom(nri, rs) == true;
    
    predicate Iterator_removals(list<int> indices) =
        [_]frac |-> 1 &*& [1/2]removals |-> indices;
    
    @*/
    
    ArrayListIterator(ArrayList<T> list)
        //@ requires [?f]list.List(?es);
        /*@ ensures Iterator((seq_of_list)(es), none, 0) &*& (f == 1 ? Iterator_removals(nil) : true) &*& 
                    [_]this.list |-> list &*& [_]oldElements |-> es &*& [_]frac |-> f &*&
                    Iterable_iterating(ArrayList.class)(list, es, f, this);
        @*/
    {
        this.list = list;
        //@ frac = f;
        //@ oldElements = es;
        //@ removals = nil;
        //@ leak this.list |-> _ &*& frac |-> _ &*& oldElements |-> _;
        //@ close Iterable_iterating(ArrayList.class) (list, es, f, this);
    }
    
    public boolean hasNext()
        //@ requires Iterator(?es, ?c, ?n);
        //@ ensures Iterator(es, c, n) &*& result ? es(n) != none : es(n) == none; // Force case split.
    {
        return index < list.size();
        //@ switch (removals) { case nil: case cons(r, rs1): }
        //@ length_remove_nths(removals, oldElements);
        
    }
    
    public T next()
        //@ requires Iterator(?es, ?c, ?n) &*& es(n) != none;
        //@ ensures Iterator(es, some(n), n + 1) &*& result == the(es(n));
    {
        //@ list.size_limits();
        //@ switch (removals) { case nil: case cons(r, rs1): }
        //@ length_remove_nths(removals, oldElements);
        //@ assert [_]oldElements |-> ?oes;
        //@ seq_of_list_length(oes, n);
        return list.get(index++);
        //@ hasCurrentElement = true;
        //@ nextRemoveIndex = n;
        //@ nth_remove_nths(n, removals, oldElements);
    }
    
    public void remove()
        //@ requires Iterator(?es, ?c, ?n) &*& Iterator_removals(?rs) &*& c != none;
        //@ ensures Iterator(es, none, n) &*& Iterator_removals(cons(the(c), rs));
    {
        //@ open Iterator_removals(_);
        list.remove(--index);
        //@ removals = cons(the(c), rs);
        //@ hasCurrentElement = false;
        //@ nextRemoveIndex = n;
        //@ remove_nth_remove_nths(the(c), rs, oldElements);
        //@ length_remove_nths(cons(the(c), rs), oldElements);
    }
    
}

/*@

lemma int list_neq_nth<t>(list<t> xs, list<t> ys)
    requires length(xs) == length(ys) &*& xs != ys;
    ensures 0 <= result &*& result < length(xs) &*& nth(result, xs) != nth(result, ys);
{
    switch (xs) {
        case nil:
            switch (ys) { case nil: case cons(y0, ys0): }
        case cons(x0, xs0):
            switch (ys) {
                case nil:
                case cons(y0, ys0):
                    if (x0 != y0) {
                        return 0;
                    } else {
                        return list_neq_nth(xs0, ys0) + 1;
                    }
            }
    }
}

@*/

/*@

predicate_family_instance Iterable_iterating(ArrayList.class)(ArrayList list, list<Object> elements, real frac, ArrayListIterator it) =
    [_]it.list |-> list &*& [_]it.oldElements |-> elements &*& [_]it.frac |-> frac &*& it.getClass() == ArrayListIterator.class;

@*/

final class ArrayList<T> implements List<T> {

    Object[] elements;
    int size;
    
    /*@
    predicate Iterable(list<Object> elements) =
        List(elements);

    predicate List(list<Object> elements) =
        this.elements |-> ?e &*& this.size |-> ?s &*&
        array_slice(e, 0, s, elements) &*&
        array_slice(e, s, e.length, _);
    
    lemma void listToIterable()
        requires [?f]List(?es);
        ensures  [f]Iterable(es);
    {
        close [f]Iterable(es);
    }
    
    lemma void iterableToList()
        requires [?f]Iterable(?es);
        ensures  [f]List(es);
    {
        open [f]Iterable(es);
    }
    
    @*/

    public ArrayList()
        //@ requires true;
        //@ ensures List(nil);
    {
        elements = new Object[10];
        //@ close Iterable(nil);
        //@ iterableToList();
    }
    
    public int size()
        //@ requires [?f]List(?es);
        //@ ensures [f]List(es) &*& result == length(es);
    {
        //@ listToIterable();
        return size;
        //@ iterableToList();
    }
    
    public T get(int index)
        //@ requires [?f]List(?es) &*& 0 <= index &*& index < length(es);
        //@ ensures [f]List(es) &*& result == nth(index, es);
    {
        return elements[index];
    }
    
    public Iterator<T> iterator()
        //@ requires [?f]Iterable(?es);
        /*@
        ensures
            result.Iterator((seq_of_list)(es), none, 0) &*&
            (f == 1 ? result.Iterator_removals(nil) : true) &*&
            Iterable_iterating(this.getClass())(this, es, f, result);
        @*/
    {
        //@ this.iterableToList();
        ArrayListIterator<T> i = new ArrayListIterator<T>(this);
        //@ close Iterable_iterating(ArrayList.class)(this, es, f, i);
        return i;
    }
    
    /*@
    
    lemma void destroyIterator()
        requires Iterable_iterating(this.getClass())(this, ?es, 1, ?it) &*& it.Iterator(_, _, _) &*& it.Iterator_removals(?rs);
        ensures Iterable(remove_nths(rs, es));
    {
        open Iterable_iterating(ArrayList.class)(_, _, _, ?iter);
        open iter.Iterator(_, _, _);
        open iter.Iterator_removals(_);
        close List(remove_nths(rs, es));
    }
    
    lemma void destroyIteratorFrac()
        requires Iterable_iterating(this.getClass())(this, ?es, ?f, ?it) &*& it.Iterator(_, _, _) &*& f < 1;
        ensures [f]Iterable(es);
    {
        open Iterable_iterating(ArrayList.class)(_, _, _, ?iter);
        open iter.Iterator(_, _, _);
    }
    
    @*/

    boolean add(T e)
        //@ requires List(?es);
        //@ ensures List(append(es, cons(e, nil))) &*& result;
    {
        if (size == elements.length) {
            Object[] newArray = new Object[2 * size + 1];
            //@ close array_slice_dynamic(array_slice_Object, elements, 0, size, _);
            //@ close array_slice_dynamic(array_slice_Object, newArray, 0, size, _);
            //@ close arraycopy_pre(array_slice_Object, false, 1, elements, 0, size, _, newArray, 0);
            System.arraycopy(elements, 0, newArray, 0, size);
            //@ open arraycopy_post(_, _, _, _, _, _, _, _, _);
            //@ open array_slice_dynamic(array_slice_Object, newArray, _, _, _);
            elements = newArray;
        }
        elements[size++] = e;
        return true;
    }
    
    boolean addAll(Collection<T> other)
        //@ requires List(?es) &*& listIsCollection(?li, other) &*& li.List(?other_es);
        //@ ensures List(append(es, other_es)) &*& li.List(other_es);
    {
        //@ open listIsCollection(li, other);
        List l = (List) other;
        int n = l.size();
        //@ list<Object> ys = nil;
        //@ list<Object> zs = other_es;
        for (int i = 0; i < n; i++)
            //@ requires List(?xs) &*& l.List(append(ys, zs)) &*& length(ys) == i &*& length(ys) + length(zs) == n &*& switch (zs) { case nil: return true; case cons(h, t): return true; };
            //@ ensures List(append(xs, old_zs)) &*& l.List(append(old_ys, old_zs));
        {
            add(l.get(i));
            //@ assert zs == cons(?h, ?t);
            //@ append_assoc(ys, {h}, t);
            //@ ys = append(ys, {h});
            //@ zs = t;
            //@ append_assoc(xs, {h}, t);
        }
        return true;
    }
    
    T remove(int index)
        //@ requires List(?es) &*& 0 <= index &*& index < length(es);
        //@ ensures List(remove_nth(index, es)) &*& result == nth(index, es);
    {
        T result = elements[index];
        /*@
        if (index + 1 == size) {
            close array_slice_dynamic(array_slice_Object, elements, index + 1, index + 1, array_slice_Objects(nil));
            close array_slice_dynamic(array_slice_Object, elements, index, index, array_slice_Objects(nil));
            close arraycopy_pre(array_slice_Object, false, 1, elements, index + 1, 0, array_slice_Objects(nil), elements, index);
        } else {
            close array_slice_dynamic(array_slice_Object, elements, index, index + 1, _);
            assert elements |-> ?e &*& size |-> ?s &*& array_slice(e, index + 1, s, ?elems);
            close array_slice_dynamic(array_slice_Object, elements, index + 1, size - 1, _);
            close array_slice_dynamic(array_slice_Object, elements, size - 1, size, _);
            close arraycopy_pre(array_slice_Object, true, 1, elements, index + 1, size - index - 1, array_slice_Objects(elems), elements, index);
        }
        @*/
        System.arraycopy(elements, index + 1, elements, index, size - index - 1);
        //@ open arraycopy_post(_, _, _, _, _, _, _, _, _);
        //@ open array_slice_dynamic(_, _, _, _, _);
        //@ open array_slice_dynamic(_, _, _, _, _);
        elements[--size] = null;
        return result;
        //@ remove_nth_take_drop(es, index);
    }
    
    /*@
    
    lemma void size_limits()
        requires [?f]List(?es);
        ensures [f]List(es) &*& length(es) <= Integer.MAX_VALUE;
    {
        open List(es);
    }
    
    @*/
    
}