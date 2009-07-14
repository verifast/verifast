#include "stdlib.h"
#include "atomics.h"
#include "list.h"
#include "ghost_lists.h"
#include "locks.h"
#include "lcset.h"

struct node {
    void *lock;
    //@ struct node *oldNext;
    struct node *next;
    int value;
};

struct set {
    struct node *head;
    //@ int nodesList;
};

/*@

lemma void match_fractions_set_head(struct set *set);
    requires [?f1]set_head(set, ?head1) &*& [?f2]set_head(set, ?head2);
    ensures [f1]set_head(set, head1) &*& [f2]set_head(set, head2) &*& head1 == head2;

lemma void match_fractions_set_nodesList(struct set *set);
    requires [?f1]set_nodesList(set, ?nodesList1) &*& [?f2]set_nodesList(set, ?nodesList2);
    ensures
        [f1]set_nodesList(set, nodesList1) &*& [f2]set_nodesList(set, nodesList2) &*&
        nodesList1 == nodesList2;

@*/

/*@

predicate lseg(int nodesList, struct node *first, int firstValue, struct node *last, int lastValue, list<struct node *> nodes, list<int> values) =
    switch (values) {
        case nil: return first == last &*& nodes == nil &*& firstValue == lastValue;
        case cons(value, values0): return
            firstValue == value &*&
            malloc_block_node(first) &*&
            [?f]first->oldNext |-> ?oldNext &*&
            [f/2]first->value |-> firstValue &*&
            [f]first->lock |-> ?lock &*&
            [f/2]oldNext->value |-> ?nextValue &*&
            value < nextValue &*&
            (
                lock == 0 ?
                    first->next |-> oldNext &*& f == 1 &*&
                    ghost_list_member_handle(nodesList, first)
                :
                    f == 1/2
            ) &*&
            lseg(nodesList, oldNext, nextValue, last, lastValue, ?nodes0, values0) &*& nodes == cons(first, nodes0);
    };

lemma void lseg_split(struct node *node)
    requires lseg(?nodesList, ?first, ?firstValue, ?last, ?lastValue, ?nodes, ?values) &*& mem(node, nodes) == true;
    ensures
        lseg(nodesList, node, ?nodeValue, last, lastValue, ?nodes1, ?values1) &*&
        lseg(nodesList, first, firstValue, node, nodeValue, ?nodes0, ?values0) &*&
        nodes1 != nil &*& head(nodes1) == node &*& values1 != nil &*& head(values1) == nodeValue &*&
        nodes == append(nodes0, nodes1) &*& values == append(values0, values1);
{
    if (first == node) {
        open lseg(_, _, _, _, _, _, _);
        close lseg(nodesList, first, firstValue, first, firstValue, nil, nil);
        close lseg(nodesList, first, firstValue, last, lastValue, nodes, values);
    } else {
        open lseg(_, _, _, _, _, _, _);
        lseg_split(node);
        assert [_]first->oldNext |-> ?oldNext;
        assert lseg(nodesList, oldNext, ?nextValue, node, ?nodeValue, ?nodes0, ?values0);
        close lseg(nodesList, first, firstValue, node, nodeValue, cons(first, nodes0), cons(firstValue, values0));
    }
}

lemma void lseg_merge(struct node *node)
    requires
        lseg(?nodesList, ?first, ?firstValue, node, ?nodeValue, ?nodes0, ?values0) &*&
        lseg(nodesList, node, nodeValue, ?last, ?lastValue, ?nodes1, ?values1);
    ensures
        lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1));
{
    open lseg(nodesList, first, firstValue, node, nodeValue, nodes0, values0);
    if (values0 == nil) {
    } else {
        lseg_merge(node);
        close lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1));
    }
}

lemma void lseg_merge2(struct node *node, int e, list<int> values10)
    requires
        lseg(?nodesList, ?first, ?firstValue, node, ?nodeValue, ?nodes0, ?values0) &*&
        lseg(nodesList, node, nodeValue, ?last, ?lastValue, ?nodes1, ?values1) &*&
        values1 == add_sorted(e, values10) &*& nodeValue < e;
    ensures
        lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1)) &*&
        firstValue < e &*&
        append(values0, values1) == add_sorted(e, append(values0, values10)) &*&
        mem_sorted(e, append(values0, values10)) == mem_sorted(e, values10);
{
    open lseg(nodesList, first, firstValue, node, nodeValue, nodes0, values0);
    if (values0 == nil) {
    } else {
        lseg_merge2(node, e, values10);
        close lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1));
    }
}

lemma void lseg_merge3(struct node *node, int e, list<int> values10)
    requires
        lseg(?nodesList, ?first, ?firstValue, node, ?nodeValue, ?nodes0, ?values0) &*&
        lseg(nodesList, node, nodeValue, ?last, ?lastValue, ?nodes1, ?values1) &*&
        values1 == remove_sorted(e, values10) &*& nodeValue < e;
    ensures
        lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1)) &*&
        firstValue < e &*&
        append(values0, values1) == remove_sorted(e, append(values0, values10)) &*&
        mem_sorted(e, append(values0, values10)) == mem_sorted(e, values10);
{
    open lseg(nodesList, first, firstValue, node, nodeValue, nodes0, values0);
    if (values0 == nil) {
    } else {
        lseg_merge3(node, e, values10);
        close lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1));
    }
}

predicate set(struct set *set) =
    [1/2]set->head |-> ?head &*& [1/2]set->nodesList |-> _ &*& [1/2]head->value |-> _ &*& malloc_block_set(set);

predicate set_atomic(struct set *set, list<int> values) =
    [1/2]set->head |-> ?head &*&
    [1/2]set->nodesList |-> ?nodesList &*&
    ghost_list(nodesList, ?nodes) &*&
    lseg(nodesList, head, MIN_INT, ?tail, MAX_INT, nodes, cons(MIN_INT, values)) &*&
    head != tail &*&
    tail->lock |-> _ &*& tail->oldNext |-> _ &*& tail->next |-> _ &*& [1/2]tail->value |-> MAX_INT &*& malloc_block_node(tail);
@*/

struct set *create_set()
    //@ requires true;
    //@ ensures set(result) &*& set_atomic(result, nil);
{
    struct node *first = malloc(sizeof(struct node));
    if (first == 0) abort();
    struct node *last = malloc(sizeof(struct node));
    if (last == 0) abort();
    first->lock = 0;
    first->value = MIN_INT;
    //@ first->oldNext = last;
    first->next = last;
    last->value = MAX_INT;
    struct set *set = malloc(sizeof(struct set));
    if (set == 0) abort();
    set->head = first;
    //@ split_fraction set_head(set, _);
    //@ int nodesList = create_ghost_list<struct node *>();
    //@ ghost_list_insert(nodesList, nil, nil, first);
    //@ set->nodesList = nodesList;
    //@ split_fraction set_nodesList(set, _);
    //@ split_fraction node_value(first, _);
    //@ split_fraction node_value(last, _);
    //@ close set(set);
    //@ close lseg(nodesList, last, MAX_INT, last, MAX_INT, nil, nil);
    //@ close lseg(nodesList, first, MIN_INT, last, MAX_INT, cons(first, nil), cons(MIN_INT, nil));
    //@ close set_atomic(set, nil);
    return set;
}

void dispose_set(struct set *set)
    //@ requires set(set) &*& set_atomic(set, ?values);
    //@ ensures true;
{
    //@ open set(set);
    //@ open set_atomic(set, values);
    //@ merge_fractions set_head(set, _);
    //@ merge_fractions set_nodesList(set, ?nodesList);
    //@ assert lseg(_, _, _, ?last, _, _, _);
    struct node *x = set->head;
    while (x->value < MAX_INT)
        /*@
        invariant
            lseg(nodesList, x, _, last, MAX_INT, _, _) &*&
            [1/2]x->value |-> ?xValue &*& [1/2]last->value |-> MAX_INT;
        @*/
    {
        //@ open lseg(_, _, _, _, _, _, _);
        //@ merge_fractions node_value(x, _);
        //@ assert [_]node_lock(x, ?lockValue);
        //@ assume(lockValue == 0); // TODO: Eliminate this assume statement.
        struct node *y = x->next;
        free(x);
        //@ leak ghost_list_member_handle(nodesList, x);
        x = y;
    }
    {
        /*@
        lemma void iter()
            requires lseg(nodesList, ?z, _, last, MAX_INT, _, _) &*& [1/2]z->value |-> ?zValue &*& zValue >= MAX_INT &*& [1/2]last->value |-> MAX_INT;
            ensures z == last &*& zValue == MAX_INT &*& last->value |-> MAX_INT;
        {
            open lseg(_, _, _, _, _, _, ?values_);
            if (values_ == nil) {
                merge_fractions node_value(z, _);
            } else {
                merge_fractions node_value(z, _);
                assert [_]node_lock(z, ?lockValue);
                assume(lockValue == 0); // TODO: Eliminate this assume statement.
                iter();
            }
        }
        @*/
        //@ iter();
    }
    free(x);
    free(set);
    //@ leak ghost_list(nodesList, _);
}

struct node *locate(struct set *set, int e)
    /*@
    requires
        MIN_INT < e &*&
        [?fSet]set->head |-> ?head &*&
        [fSet]set->nodesList |-> ?nodesList &*&
        [?f]atomic_space(?inv) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep);
    @*/
    /*@
    ensures
        [fSet]set->head |-> head &*&
        [fSet]set->nodesList |-> nodesList &*&
        [f]atomic_space(inv) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        ghost_list_member_handle(nodesList, result) &*&
        [1/2]result->lock |-> (void *)1 &*&
        [1/2]result->oldNext |-> ?next &*&
        result->next |-> next &*&
        [1/4]result->value |-> ?resultValue &*&
        [1/4]next->value |-> ?nextValue &*&
        resultValue < e &*& e <= nextValue;
    @*/
{
    struct node *p = set->head;
    {
        /*@
        predicate_family_instance lock_context_pre(context)(predicate() inv_, void **lock) =
            inv_ == inv &*& lock == &p->lock &*&
            [fSet]set->head |-> head &*&
            [fSet]set->nodesList |-> nodesList &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep);
        predicate_family_instance lock_context_post(context)() =
            [fSet]set->head |-> head &*&
            [fSet]set->nodesList |-> nodesList &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
            ghost_list_member_handle(nodesList, p) &*&
            [1/2]p->oldNext |-> ?next &*&
            [1/2]p->lock |-> (void *)1 &*&
            p->next |-> next &*&
            [1/4]p->value |-> ?pValue &*&
            [1/4]next->value |-> ?nextValue &*&
            pValue < e;
        lemma void context(lock_operation *op) : lock_context
            requires
                lock_context_pre(context)(?inv_, ?lock) &*& inv_() &*&
                is_lock_operation(op) &*& lock_operation_pre(op)(lock);
            ensures
                is_lock_operation(op) &*& lock_operation_post(op)(?success) &*& inv_() &*&
                success ? lock_context_post(context)() : lock_context_pre(context)(inv_, lock);
        {
            open lock_context_pre(context)(_, _);
            sep();
            open set_atomic(set, ?values);
            match_fractions_set_head(set);
            match_fractions_set_nodesList(set);
            open lseg(nodesList, head, MIN_INT, ?last, MAX_INT, ?nodes, ?values_);
            open [?fPointer]node_lock(head, _);
            op();
            assert [_]pointer(&head->lock, ?lockValue);
            close [fPointer]node_lock(head, lockValue);
            assert lock_operation_post(op)(?success);
            if (success) {
                split_fraction node_oldNext(head, ?oldNext);
                split_fraction node_value(head, _);
                split_fraction node_lock(head, _);
                split_fraction node_value(oldNext, _);
                close lseg(nodesList, head, MIN_INT, last, MAX_INT, nodes, values_);
                close set_atomic(set, values);
                unsep();
                close lock_context_post(context)();
            } else {
                close lseg(nodesList, head, MIN_INT, last, MAX_INT, nodes, values_);
                close set_atomic(set, values);
                unsep();
                close lock_context_pre(context)(inv, &head->lock);
            }
        }
        @*/
        //@ close lock_context_pre(context)(inv, &p->lock);
        //@ produce_lemma_function_pointer_chunk(context);
        lock(&p->lock);
        //@ leak is_lock_context(context);
        //@ open lock_context_post(context)();
    }
loop:
    /*@
    invariant
        [fSet]set->head |-> head &*&
        [fSet]set->nodesList |-> nodesList &*&
        [f]atomic_space(inv) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        ghost_list_member_handle(nodesList, p) &*&
        [1/2]p->oldNext |-> ?next &*&
        [1/2]p->lock |-> (void *)1 &*&
        p->next |-> next &*&
        [1/4]p->value |-> ?pValue &*&
        [1/4]next->value |-> ?nextValue &*&
        pValue < e;
    @*/
    struct node *c = p->next;
    //@ assume_is_int(e);
    if (c->value < e) {
        {
            /*@
            predicate_family_instance lock_context_pre(context)(predicate() inv_, void **lock) =
                inv_ == inv &*& lock == &c->lock &*&
                [fSet]set->head |-> head &*&
                [fSet]set->nodesList |-> nodesList &*&
                is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
                ghost_list_member_handle(nodesList, p) &*&
                [1/2]p->oldNext |-> next &*&
                [1/2]p->lock |-> (void *)1 &*&
                p->next |-> next &*&
                [1/4]p->value |-> pValue &*&
                [1/4]next->value |-> nextValue;
            predicate_family_instance lock_context_post(context)() =
                [fSet]set->head |-> head &*&
                [fSet]set->nodesList |-> nodesList &*&
                is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
                ghost_list_member_handle(nodesList, p) &*&
                [1/2]p->oldNext |-> next &*&
                [1/2]p->lock |-> (void *)1 &*&
                p->next |-> next &*&
                [1/4]p->value |-> pValue &*&
                [1/4]next->value |-> nextValue &*&
                ghost_list_member_handle(nodesList, c) &*&
                [1/2]c->oldNext |-> ?nextNext &*&
                [1/2]c->lock |-> (void *)1 &*&
                c->next |-> nextNext &*&
                [1/4]c->value |-> nextValue &*&
                [1/4]nextNext->value |-> ?nextNextValue;
            lemma void context(lock_operation *op) : lock_context
                requires
                    lock_context_pre(context)(?inv_, ?lock) &*& inv_() &*&
                    is_lock_operation(op) &*& lock_operation_pre(op)(lock);
                ensures
                    is_lock_operation(op) &*& lock_operation_post(op)(?success) &*& inv_() &*&
                    success ? lock_context_post(context)() : lock_context_pre(context)(inv_, lock);
            {
                open lock_context_pre(context)(_, _);
                sep();
                open set_atomic(set, ?values);
                match_fractions_set_head(set);
                match_fractions_set_nodesList(set);
                ghost_list_member_handle_lemma();
                lseg_split(p);
                open lseg(nodesList, p, ?pValue0, ?last, MAX_INT, ?nodes1, ?values1);
                merge_fractions node_oldNext(p, _);
                split_fraction node_oldNext(p, _);
                merge_fractions node_value(c, _);
                split_fraction node_value(c, _);
                open lseg(nodesList, c, ?cValue, last, MAX_INT, ?nodes2, ?values2);
                open node_lock(c, _);
                op();
                assert [?fPointer]pointer(&c->lock, ?lockValue);
                close [fPointer]node_lock(c, lockValue);
                assert lock_operation_post(op)(?success);
                if (success) {
                    split_fraction node_lock(c, _);
                    split_fraction node_oldNext(c, ?cNext);
                    split_fraction node_value(c, _);
                    split_fraction node_value(cNext, _);
                    close lseg(nodesList, c, cValue, last, MAX_INT, nodes2, values2);
                    close lseg(nodesList, p, pValue0, last, MAX_INT, nodes1, values1);
                    lseg_merge(p);
                    close set_atomic(set, values);
                    unsep();
                    merge_fractions node_value(c, _);
                    split_fraction node_value(c, _);
                    close lock_context_post(context)();
                } else {
                    close lseg(nodesList, c, cValue, last, MAX_INT, nodes2, values2);
                    close lseg(nodesList, p, pValue0, last, MAX_INT, nodes1, values1);
                    lseg_merge(p);
                    close set_atomic(set, values);
                    unsep();
                    close lock_context_pre(context)(inv, &c->lock);
                }
            }
            @*/
            //@ close lock_context_pre(context)(inv, &c->lock);
            //@ produce_lemma_function_pointer_chunk(context);
            lock(&c->lock);
            //@ leak is_lock_context(context);
            //@ open lock_context_post(context)();
        }
        {
            /*@
            predicate_family_instance atomic_store_pointer_context_pre(context)(predicate() inv_, void **pp, void *p_) =
                inv_ == inv &*& pp == &p->lock &*& p_ == 0 &*&
                [fSet]set->head |-> head &*&
                [fSet]set->nodesList |-> nodesList &*&
                is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
                ghost_list_member_handle(nodesList, p) &*&
                [1/2]p->oldNext |-> next &*&
                [1/2]p->lock |-> (void *)1 &*&
                p->next |-> next &*&
                [1/4]p->value |-> pValue &*&
                [1/4]next->value |-> nextValue;
            predicate_family_instance atomic_store_pointer_context_post(context)() =
                [fSet]set->head |-> head &*&
                [fSet]set->nodesList |-> nodesList &*&
                is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep);
            lemma void context(atomic_store_pointer_operation *op) : atomic_store_pointer_context
                requires
                    atomic_store_pointer_context_pre(context)(?inv_, ?pp, ?p_) &*& inv_() &*&
                    is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_pre(op)(pp, p_);
                ensures
                    atomic_store_pointer_context_post(context)() &*& inv_() &*&
                    is_atomic_store_pointer_operation(op) &*& atomic_store_pointer_operation_post(op)();
            {
                open atomic_store_pointer_context_pre(context)(_, _, _);
                sep();
                open set_atomic(set, ?values);
                match_fractions_set_head(set);
                match_fractions_set_nodesList(set);
                ghost_list_member_handle_lemma();
                lseg_split(p);
                open lseg(nodesList, p, _, ?last, MAX_INT, ?nodes1, ?values1);
                merge_fractions node_lock(p, _);
                merge_fractions node_value(p, _);
                merge_fractions node_oldNext(p, _);
                merge_fractions node_value(c, _);
                open node_lock(p, _);
                op();
                close node_lock(p, 0);
                close lseg(nodesList, p, pValue, last, MAX_INT, nodes1, values1);
                lseg_merge(p);
                close set_atomic(set, values);
                unsep();
                close atomic_store_pointer_context_post(context)();
            }
            @*/
            //@ close atomic_store_pointer_context_pre(context)(inv, &p->lock, 0);
            //@ produce_lemma_function_pointer_chunk(context);
            unlock(&p->lock);
            //@ leak is_atomic_store_pointer_context(context);
            //@ open atomic_store_pointer_context_post(context)();
        }
        p = c;
        goto loop;
    }
    return p;
}

bool add(struct set *set, int e)
    /*@
    requires
        MIN_INT < e &*& e < MAX_INT &*&
        [?f]atomic_space(?inv) &*&
        [?fSet]set(set) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep) &*&
        is_set_add(?op) &*& set_add_pre(op)(unsep, info, e);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [fSet]set(set) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        is_set_add(op) &*& set_add_post(op)(result);
    @*/
{
    //@ open set(set);
    //@ assert [_]set->nodesList |-> ?nodesList;
    struct node *head = set->head;
    struct node *x = locate(set, e);
    struct node *z = x->next;
    bool result = false;
    struct node *y = 0;
    //@ assert [_]x->value |-> ?xValue;
    //@ assert [_]z->value |-> ?zValue;
    if (z->value != e) {
        y = malloc(sizeof(struct node));
        if (y == 0) abort();
        y->lock = 0;
        y->value = e;
        //@ y->oldNext = z;
        y->next = z;
        x->next = y;
        result = true;
    }
    {
        /*@
        predicate_family_instance atomic_store_pointer_context_pre(context)(predicate() inv_, void **pp, void *p_) =
            inv_ == inv &*& pp == &x->lock &*& p_ == 0 &*&
            [fSet/2]set->head |-> head &*&
            [fSet/2]set->nodesList |-> nodesList &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
            is_set_add(op) &*& set_add_pre(op)(unsep, info, e) &*&
            ghost_list_member_handle(nodesList, x) &*&
            [1/2]x->lock |-> (void *)1 &*&
            [1/2]x->oldNext |-> z &*&
            [1/4]x->value |-> xValue &*&
            [1/4]z->value |-> zValue &*&
            zValue != e ?
                malloc_block_node(y) &*&
                y->lock |-> 0 &*&
                y->oldNext |-> z &*&
                y->value |-> e &*&
                y->next |-> z &*&
                x->next |-> y
            :
                x->next |-> z;
        predicate_family_instance atomic_store_pointer_context_post(context)() =
            [fSet/2]set->head |-> head &*&
            [fSet/2]set->nodesList |-> nodesList &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
            is_set_add(op) &*& set_add_post(op)(zValue != e);
        lemma void context(atomic_store_pointer_operation *sop) : atomic_store_pointer_context
            requires
                atomic_store_pointer_context_pre(context)(?inv_, ?pp, ?p_) &*& inv_() &*&
                is_atomic_store_pointer_operation(sop) &*& atomic_store_pointer_operation_pre(sop)(pp, p_);
            ensures
                atomic_store_pointer_context_post(context)() &*& inv_() &*&
                is_atomic_store_pointer_operation(sop) &*& atomic_store_pointer_operation_post(sop)();
        {
            open atomic_store_pointer_context_pre(context)(_, _, _);
            sep();
            open set_atomic(set, ?values);
            match_fractions_set_head(set);
            match_fractions_set_nodesList(set);
            ghost_list_member_handle_lemma();
            lseg_split(x);
            assert lseg(nodesList, head, _, x, _, ?nodes0, ?values0);
            open lseg(nodesList, x, _, ?last, MAX_INT, ?nodes1, ?values1);
            merge_fractions node_lock(x, _);
            merge_fractions node_oldNext(x, _);
            merge_fractions node_value(x, _);
            merge_fractions node_value(z, _);
            open node_lock(x, _);
            sop();
            close node_lock(x, 0);
            open lseg(nodesList, z, zValue, last, MAX_INT, ?nodes2, ?values2);
            close lseg(nodesList, z, zValue, last, MAX_INT, nodes2, values2);
            if (zValue != e) {
                x->oldNext = y;
                split_fraction node_value(y, _);
                append_assoc_lemma(nodes0, cons(x, nil), tail(nodes1));
                ghost_list_insert(nodesList, append(nodes0, cons(x, nil)), tail(nodes1), y);
                append_assoc_lemma(nodes0, cons(x, nil), cons(y, tail(nodes1)));
                close lseg(nodesList, y, e, last, MAX_INT, cons(y, tail(nodes1)), cons(e, tail(values1)));
                close lseg(nodesList, x, xValue, last, MAX_INT, cons(x, cons(y, tail(nodes1))), cons(xValue, cons(e, tail(values1))));
                lseg_merge2(x, e, values1);
            } else {
                close lseg(nodesList, x, xValue, last, MAX_INT, nodes1, values1);
                lseg_merge2(x, e, values1);
            }
            close set_atomic(set, add_sorted(e, values));
            op();
            unsep();
            close atomic_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_store_pointer_context_pre(context)(inv, &x->lock, 0);
        //@ produce_lemma_function_pointer_chunk(context);
        unlock(&x->lock);
        //@ leak is_atomic_store_pointer_context(context);
        //@ open atomic_store_pointer_context_post(context)();
    }
    //@ close [fSet]set(set);
    return result;
}

bool remove(struct set *set, int e)
    /*@
    requires
        MIN_INT < e &*& e < MAX_INT &*&
        [?f]atomic_space(?inv) &*&
        [?fSet]set(set) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep) &*&
        is_set_remove(?op) &*& set_remove_pre(op)(unsep, info, e);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [fSet]set(set) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        is_set_remove(op) &*& set_remove_post(op)(result);
    @*/
{
    //@ open [fSet]set(set);
    //@ assert [fSet/2]set->nodesList |-> ?nodesList;
    struct node *head = set->head;
    struct node *x = locate(set, e);
    //@ assert [_]x->value |-> ?xValue;
    struct node *y = x->next;
    //@ assert [_]y->value |-> ?yValue;
    bool result = y->value == e;
    if (result) {
        {
            /*@
            predicate_family_instance lock_context_pre(context)(predicate() inv_, void **lock) =
                inv_ == inv &*& lock == &y->lock &*&
                [fSet/2]set->head |-> head &*&
                [fSet/2]set->nodesList |-> nodesList &*&
                is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
                is_set_remove(op) &*& set_remove_pre(op)(unsep, info, e) &*&
                ghost_list_member_handle(nodesList, x) &*&
                [1/2]x->oldNext |-> y &*&
                [1/2]x->lock |-> (void *)1 &*&
                [1/4]x->value |-> xValue &*&
                [1/4]y->value |-> yValue;
            predicate_family_instance lock_context_post(context)() =
                [fSet/2]set->head |-> head &*&
                [fSet/2]set->nodesList |-> nodesList &*&
                is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
                is_set_remove(op) &*& set_remove_post(op)(true) &*&
                ghost_list_member_handle(nodesList, x) &*&
                [1/2]x->oldNext |-> ?z &*&
                [1/2]x->lock |-> (void *)1 &*&
                [1/4]x->value |-> xValue &*&
                y->value |-> yValue &*&
                y->oldNext |-> z &*&
                y->lock |-> (void *)1 &*&
                y->next |-> z &*&
                [1/4]z->value |-> ?zValue &*&
                malloc_block_node(y);
            lemma void context(lock_operation *lop) : lock_context
                requires
                    lock_context_pre(context)(?inv_, ?lock) &*& inv_() &*&
                    is_lock_operation(lop) &*& lock_operation_pre(lop)(lock);
                ensures
                    is_lock_operation(lop) &*& lock_operation_post(lop)(?success) &*& inv_() &*&
                    success ? lock_context_post(context)() : lock_context_pre(context)(inv_, lock);
            {
                open lock_context_pre(context)(_, _);
                sep();
                open set_atomic(set, ?values);
                match_fractions_set_head(set);
                match_fractions_set_nodesList(set);
                ghost_list_member_handle_lemma();
                lseg_split(x);
                open lseg(nodesList, x, _, ?last, MAX_INT, ?nodes1, ?values1);
                assert lseg(nodesList, _, _, x, _, ?nodes0, ?values0);
                merge_fractions node_lock(x, _);
                split_fraction node_lock(x, _);
                merge_fractions node_value(x, _);
                split_fraction node_value(x, _);
                merge_fractions node_oldNext(x, _);
                merge_fractions node_value(y, _);
                open lseg(nodesList, y, _, last, MAX_INT, ?nodes2, ?values2);
                open node_lock(y, _);
                lop();
                assert [?fPointer]pointer(&y->lock, ?lockValue);
                close [fPointer]node_lock(y, lockValue);
                assert lock_operation_post(lop)(?success);
                if (success) {
                    struct node *z = y->oldNext;
                    x->oldNext = z;
                    split_fraction node_oldNext(x, _);
                    split_fraction node_value(z, _);
                    close lseg(nodesList, x, xValue, last, MAX_INT, cons(x, tail(nodes2)), cons(xValue, tail(values2)));
                    lseg_merge3(x, e, values1);
                    append_assoc_lemma(nodes0, cons(x, nil), nodes2);
                    ghost_list_remove(nodesList, append(nodes0, cons(x, nil)), tail(nodes2), y);
                    append_assoc_lemma(nodes0, cons(x, nil), tail(nodes2));
                    close set_atomic(set, remove_sorted(e, values));
                    op();
                    unsep();
                    merge_fractions node_value(y, _);
                    close lock_context_post(context)();
                } else {
                    close lseg(nodesList, y, yValue, last, MAX_INT, nodes2, values2);
                    split_fraction node_oldNext(x, _);
                    split_fraction node_value(y, _);
                    close lseg(nodesList, x, xValue, last, MAX_INT, nodes1, values1);
                    lseg_merge(x);
                    close set_atomic(set, values);
                    unsep();
                    close lock_context_pre(context)(inv, &y->lock);
                }
            }
            @*/
            //@ close lock_context_pre(context)(inv, &y->lock);
            //@ produce_lemma_function_pointer_chunk(context);
            lock(&y->lock);
            //@ leak is_lock_context(context);
            //@ open lock_context_post(context)();
        }
        x->next = y->next;
        free(y);
    }
    {
        /*@
        predicate_family_instance atomic_store_pointer_context_pre(context)(predicate() inv_, void **pp, void *p_) =
            inv_ == inv &*& pp == &x->lock &*& p_ == 0 &*&
            [fSet/2]set->head |-> head &*&
            [fSet/2]set->nodesList |-> nodesList &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
            ghost_list_member_handle(nodesList, x) &*&
            [1/2]x->lock |-> (void *)1 &*&
            [1/4]x->value |-> xValue &*&
            [1/2]x->oldNext |-> ?next &*&
            x->next |-> next &*&
            [1/4]next->value |-> ?nextValue &*&
            result ?
                is_set_remove(op) &*& set_remove_post(op)(true)
            :
                is_set_remove(op) &*& set_remove_pre(op)(unsep, info, e) &*&
                next == y &*& nextValue == yValue;
        predicate_family_instance atomic_store_pointer_context_post(context)() =
            [fSet/2]set->head |-> head &*&
            [fSet/2]set->nodesList |-> nodesList &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
            is_set_remove(op) &*& set_remove_post(op)(result);
        lemma void context(atomic_store_pointer_operation *sop) : atomic_store_pointer_context
            requires
                atomic_store_pointer_context_pre(context)(?inv_, ?pp, ?p_) &*& inv_() &*&
                is_atomic_store_pointer_operation(sop) &*& atomic_store_pointer_operation_pre(sop)(pp, p_);
            ensures
                atomic_store_pointer_context_post(context)() &*& inv_() &*&
                is_atomic_store_pointer_operation(sop) &*& atomic_store_pointer_operation_post(sop)();
        {
            open atomic_store_pointer_context_pre(context)(_, _, _);
            sep();
            open set_atomic(set, ?values);
            match_fractions_set_head(set);
            match_fractions_set_nodesList(set);
            ghost_list_member_handle_lemma();
            lseg_split(x);
            open lseg(nodesList, x, _, ?last, MAX_INT, ?nodes1, ?values1);
            merge_fractions node_lock(x, _);
            merge_fractions node_value(x, _);
            merge_fractions node_oldNext(x, ?next);
            merge_fractions node_value(next, ?nextValue);
            open node_lock(x, _);
            sop();
            close node_lock(x, 0);
            open lseg(nodesList, next, nextValue, last, MAX_INT, ?nodes2, ?values2);
            close lseg(nodesList, next, nextValue, last, MAX_INT, nodes2, values2);
            close lseg(nodesList, x, xValue, last, MAX_INT, nodes1, values1);
            if (result)
                lseg_merge(x);
            else {
                lseg_merge3(x, e, values1);
                op();
            }
            close set_atomic(set, values);
            unsep();
            close atomic_store_pointer_context_post(context)();
        }
        @*/
        //@ close atomic_store_pointer_context_pre(context)(inv, &x->lock, 0);
        //@ produce_lemma_function_pointer_chunk(context);
        unlock(&x->lock);
        //@ leak is_atomic_store_pointer_context(context);
        //@ open atomic_store_pointer_context_post(context)();
    }
    //@ close [fSet]set(set);
    return result;
}
