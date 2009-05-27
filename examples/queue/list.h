#ifndef LIST_H
#define LIST_H

/*@

inductive list<t> = nil | cons(t, list<t>);

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

@*/

#endif