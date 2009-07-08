#ifndef LIST_H
#define LIST_H

/*@

inductive list<t> = nil | cons(t, list<t>);

fixpoint t ith<t>(int i, list<t> xs) {
    switch (xs) {
        case nil: return default<t>;
        case cons(x, xs0): return i == 0 ? x : ith(i - 1, xs0);
    }
}

fixpoint int length<t>(list<t> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return 1 + length(xs0);
    }
}

lemma void length_nonnegative<a>(list<a> xs);
    requires true;
    ensures 0 <= length(xs);

fixpoint list<t> append<t>(list<t> vs1, list<t> vs2) {
    switch (vs1) {
        case nil: return vs2;
        case cons(h, t): return cons(h, append(t, vs2));
    }
}

fixpoint list<t> reverse<t>(list<t> vs) {
    switch (vs) {
        case nil: return nil;
        case cons(h, t): return append(reverse(t), cons(h, nil));
    }
}

fixpoint t reverseHead<t>(t head, list<t> tail) {
    switch (tail) {
        case nil: return head;
        case cons(h, t): return reverseHead(h, t);
    }
}

fixpoint list<t> reverseTail<t>(t head, list<t> tail) {
    switch (tail) {
        case nil: return nil;
        case cons(h, t): return append(reverseTail(h, t), cons(head, nil));
    }
}

lemma void append_assoc_lemma<t>(list<t> xs, list<t> ys, list<t> zs)
    requires true;
    ensures append(xs, append(ys, zs)) == append(append(xs, ys), zs);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            append_assoc_lemma(t, ys, zs);
    }
}

lemma void append_nil_lemma<t>(list<t> xs)
    requires true;
    ensures append(xs, nil) == xs;
{
    switch (xs) {
       case nil:
       case cons(h, t):
           append_nil_lemma(t);
    }
}

lemma void reverse_head_tail_lemma<t>(t h, list<t> t)
    requires true;
    ensures reverse(cons(h, t)) == cons(reverseHead(h, t), reverseTail(h, t));
{
    switch (t) {
        case nil:
        case cons(th, tt):
            reverse_head_tail_lemma(th, tt);
    }
}

lemma void reverse_append_lemma<t>(list<t> xs, list<t> ys)
    requires true;
    ensures reverse(append(xs, ys)) == append(reverse(ys), reverse(xs));
{
    switch (xs) {
        case nil:
            append_nil_lemma(reverse(ys));
        case cons(h, t):
            reverse_append_lemma(t, ys);
            append_assoc_lemma(reverse(ys), reverse(t), cons(h, nil));
    }
}

lemma void reverse_reverse_lemma<t>(list<t> xs)
    requires true;
    ensures reverse(reverse(xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            reverse_reverse_lemma(t);
            reverse_append_lemma(reverse(t), cons(h, nil));
    }
}

fixpoint bool mem<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return false;
        case cons(x0, xs0): return x == x0 || mem(x, xs0);
    }
}

fixpoint list<t> before<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0): return x == x0 ? nil : cons(x0, before(x, xs0));
    }
}

fixpoint list<t> after<t>(t x, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x0, xs0): return x == x0 ? xs0 : after(x, xs0);
    }
}

fixpoint list<t> take<t>(int n, list<t> xs);
fixpoint list<t> drop<t>(int n, list<t> xs);
fixpoint bool distinct<t>(list<t> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): return !mem(x, xs0) && distinct(xs0);
    }
}

lemma void drop_0<t>(list<t> xs);
    requires true;
    ensures drop(0, xs) == xs;

lemma void take_0<t>(list<t> xs);
    requires true;
    ensures take(0, xs) == nil;

lemma void drop_k_plus_one<t>(int k, list<t> xs);
    requires 0 <= k &*& k < length(xs);
    ensures drop(k, xs) == cons(ith(k, xs), drop(k + 1, xs));

lemma void drop_k_plus_one_alt<t>(int k, list<t> xs);
    requires 0 <= k &*& k <= length(xs) &*& drop(k, xs) != nil;
    ensures drop(k, xs) == cons(ith(k, xs), drop(k + 1, xs)) &*& length(xs) > k;

lemma void take_length<t>(list<t> xs);
    requires true;
    ensures take(length(xs), xs) == xs;

lemma void drop_length<t>(list<t> xs);
    requires true;
    ensures drop(length(xs), xs) == nil;

lemma void length_take<a>(int n, list<a> xs);
    requires 0 <= n &*& n <= length(xs);
    ensures length(take(n, xs)) == n;

lemma void drop_n_take_n<a>(int n, list<a> xs);
    requires true;
    ensures drop(n, take(n, xs)) == nil;

lemma void ith_take<a>(int i, int n, list<a> xs);
    requires 0 <= i &*& i <= n &*& n <= length(xs);
    ensures ith(i, take(n, xs)) == ith(i, xs);

predicate foreach<t>(list<t> xs, predicate(t) p) =
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): return p(x) &*& foreach(xs0, p);
    };

lemma void foreach_take_plus_one_unseparate<a>(int n, list<a> xs);
    requires 0 <= n &*& n < length(xs) &*& foreach(take(n, xs), ?p) &*& p(ith(n, xs));
    ensures foreach(take(n + 1, xs), p);

lemma void foreach_separate<t>(list<t> xs, t x);
    requires foreach(xs, ?p) &*& mem(x, xs) == true;
    ensures foreach(before(x, xs), p) &*& p(x) &*& foreach(after(x, xs), p);

lemma void foreach_unseparate<t>(list<t> xs, t x);
    requires mem(x, xs) == true &*& foreach(before(x, xs), ?p) &*& p(x) &*& foreach(after(x, xs), p);
    ensures foreach(xs, p);

lemma void foreach_separate_ith<t>(int i, list<t> es);
    requires foreach(es, ?p) &*& 0 <= i &*& i < length(es);
    ensures foreach(take(i, es), p) &*& p(ith(i, es)) &*& foreach(drop(i + 1, es), p);

lemma void foreach_unseparate_ith_nochange<t>(int i, list<t> es);
    requires foreach(take(i, es), ?p) &*& p(ith(i, es)) &*& foreach(drop(i + 1, es), p) &*& 0 <= i &*& i < length(es);
    ensures foreach(es, p);

predicate foreach3(list<void *> xs, list<void *> ys, list<void *>zs, predicate(void *, void *, void *) p) =
    xs == nil && ys == nil && zs == nil ?
        true
    :
        p(?x, ?y, ?z) &*& foreach3(?xs0, ?ys0, ?zs0, p) &*&
        xs == cons(x, xs0) &*&
        ys == cons(y, ys0) &*&
        zs == cons(z, zs0);

@*/

#endif