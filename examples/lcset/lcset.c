#include "stdlib.h"
#include "atomics.h"
//@ #include "ghost_lists.gh"
//@ #include "ghost_counters.gh"
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
    //@ int lockCounter;
};

/*@

predicate node_frac(struct node *node, real frac) = true;

predicate lseg(
        int nodesList,
        struct node *first,
        int firstValue,
        struct node *last,
        int lastValue,
        list<struct node *> nodes,
        list<int> values,
        int lockCount) =
    switch (values) {
        case nil: return first == last &*& nodes == nil &*& firstValue == lastValue &*& lockCount == 0;
        case cons(value, values0): return
            firstValue == value &*&
            malloc_block_node(first) &*&
            node_frac(first, ?f) &*&
            [f]first->oldNext |-> ?oldNext &*&
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
            lseg(nodesList, oldNext, nextValue, last, lastValue, ?nodes0, values0, ?lockCount0) &*&
            nodes == cons(first, nodes0) &*& 0 <= lockCount0 &*&
            lockCount == lockCount0 + (lock == 0 ? 0 : 1);
    };

lemma void lseg_split(struct node *node)
    requires lseg(?nodesList, ?first, ?firstValue, ?last, ?lastValue, ?nodes, ?values, ?lockCount) &*& mem(node, nodes) == true;
    ensures
        lseg(nodesList, node, ?nodeValue, last, lastValue, ?nodes1, ?values1, ?lockCount1) &*&
        lseg(nodesList, first, firstValue, node, nodeValue, ?nodes0, ?values0, ?lockCount0) &*&
        nodes1 != nil &*& head(nodes1) == node &*& values1 != nil &*& head(values1) == nodeValue &*&
        nodes == append(nodes0, nodes1) &*& values == append(values0, values1) &*&
        0 <= lockCount0 &*& lockCount == lockCount0 + lockCount1;
{
    if (first == node) {
        open lseg(_, _, _, _, _, _, _, _);
        close lseg(nodesList, first, firstValue, first, firstValue, nil, nil, 0);
        close lseg(nodesList, first, firstValue, last, lastValue, nodes, values, lockCount);
    } else {
        open lseg(_, _, _, _, _, _, _, _);
        lseg_split(node);
        assert [1/2]first->oldNext |-> ?oldNext;
        assert [1/2]first->lock |-> ?lock;
        assert lseg(nodesList, oldNext, ?nextValue, node, ?nodeValue, ?nodes0, ?values0, ?lockCount0);
        close lseg(nodesList, first, firstValue, node, nodeValue, cons(first, nodes0), cons(firstValue, values0), lockCount0 + (lock == 0 ? 0 : 1));
    }
}

lemma void lseg_lockCount_nonnegative()
    requires lseg(?nodesList, ?first, ?firstValue, ?last, ?lastValue, ?nodes, ?values, ?lockCount);
    ensures lseg(nodesList, first, firstValue, last, lastValue, nodes, values, lockCount) &*& 0 <= lockCount;
{
    open lseg(nodesList, first, firstValue, last, lastValue, nodes, values, lockCount);
    close lseg(nodesList, first, firstValue, last, lastValue, nodes, values, lockCount);
}

lemma void lseg_merge(struct node *node)
    requires
        lseg(?nodesList, ?first, ?firstValue, node, ?nodeValue, ?nodes0, ?values0, ?lockCount0) &*&
        lseg(nodesList, node, nodeValue, ?last, ?lastValue, ?nodes1, ?values1, ?lockCount1);
    ensures
        lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1) &*&
        0 <= lockCount0 &*& 0 <= lockCount1;
{
    open lseg(nodesList, first, firstValue, node, nodeValue, nodes0, values0, lockCount0);
    if (values0 == nil) {
        lseg_lockCount_nonnegative();
    } else {
        lseg_merge(node);
        close lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1);
    }
}

lemma void lseg_merge1(struct node *node, int e)
    requires
        lseg(?nodesList, ?first, ?firstValue, node, ?nodeValue, ?nodes0, ?values0, ?lockCount0) &*&
        lseg(nodesList, node, nodeValue, ?last, ?lastValue, ?nodes1, ?values1, ?lockCount1) &*&
        nodeValue < e;
    ensures
        lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1) &*&
        0 <= lockCount0 &*& 0 <= lockCount1 &*&
        firstValue < e &*&
        mem_sorted(e, append(values0, values1)) == mem_sorted(e, values1);
{
    open lseg(nodesList, first, firstValue, node, nodeValue, nodes0, values0, lockCount0);
    if (values0 == nil) {
        lseg_lockCount_nonnegative();
    } else {
        lseg_merge1(node, e);
        close lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1);
    }
}

lemma void lseg_merge2(struct node *node, int e, list<int> values10)
    requires
        lseg(?nodesList, ?first, ?firstValue, node, ?nodeValue, ?nodes0, ?values0, ?lockCount0) &*&
        lseg(nodesList, node, nodeValue, ?last, ?lastValue, ?nodes1, ?values1, ?lockCount1) &*&
        values1 == add_sorted(e, values10) &*& nodeValue < e;
    ensures
        lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1) &*&
        firstValue < e &*&
        append(values0, values1) == add_sorted(e, append(values0, values10)) &*&
        mem_sorted(e, append(values0, values10)) == mem_sorted(e, values10);
{
    open lseg(nodesList, first, firstValue, node, nodeValue, nodes0, values0, lockCount0);
    if (values0 == nil) {
    } else {
        lseg_merge2(node, e, values10);
        lseg_lockCount_nonnegative();
        close lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1);
    }
}

lemma void lseg_merge3(struct node *node, int e, list<int> values10)
    requires
        lseg(?nodesList, ?first, ?firstValue, node, ?nodeValue, ?nodes0, ?values0, ?lockCount0) &*&
        lseg(nodesList, node, nodeValue, ?last, ?lastValue, ?nodes1, ?values1, ?lockCount1) &*&
        values1 == remove_sorted(e, values10) &*& nodeValue < e;
    ensures
        lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1) &*&
        firstValue < e &*&
        append(values0, values1) == remove_sorted(e, append(values0, values10)) &*&
        mem_sorted(e, append(values0, values10)) == mem_sorted(e, values10);
{
    open lseg(nodesList, first, firstValue, node, nodeValue, nodes0, values0, lockCount0);
    if (values0 == nil) {
    } else {
        lseg_merge3(node, e, values10);
        lseg_lockCount_nonnegative();
        close lseg(nodesList, first, firstValue, last, lastValue, append(nodes0, nodes1), append(values0, values1), lockCount0 + lockCount1);
    }
}

predicate set(struct set *set;) =
    [1/2]set->head |-> ?head &*& [1/2]set->nodesList |-> _ &*& [1/2]head->value |-> ?headValue &*& malloc_block_set(set) &*&
    [1/2]set->lockCounter |-> ?lockCounter &*& ghost_counter_zero_contrib(lockCounter);

predicate set_atomic(struct set *set, list<int> values) =
    [1/2]set->head |-> ?head &*&
    [1/2]set->nodesList |-> ?nodesList &*&
    [1/2]set->lockCounter |-> ?lockCounter &*&
    ghost_list(nodesList, ?nodes) &*&
    ghost_counter(lockCounter, ?lockCount) &*&
    lseg(nodesList, head, INT_MIN, ?tail, INT_MAX, nodes, cons(INT_MIN, values), lockCount) &*&
    head != tail &*&
    tail->lock |-> _ &*& tail->oldNext |-> _ &*& tail->next |-> _ &*& [1/2]tail->value |-> INT_MAX &*& malloc_block_node(tail);
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
    first->value = INT_MIN;
    //@ first->oldNext = last;
    first->next = last;
    last->value = INT_MAX;
    struct set *set = malloc(sizeof(struct set));
    if (set == 0) abort();
    set->head = first;
    //@ int nodesList = create_ghost_list<struct node *>();
    //@ ghost_list_insert(nodesList, nil, nil, first);
    //@ set->nodesList = nodesList;
    //@ int lockCounter = create_ghost_counter();
    //@ set->lockCounter = lockCounter;
    //@ close set(set);
    //@ close lseg(nodesList, last, INT_MAX, last, INT_MAX, nil, nil, 0);
    //@ close node_frac(first, 1);
    //@ close lseg(nodesList, first, INT_MIN, last, INT_MAX, cons(first, nil), cons(INT_MIN, nil), 0);
    //@ close set_atomic(set, nil);
    return set;
}

void dispose_set(struct set *set)
    //@ requires set(set) &*& set_atomic(set, ?values);
    //@ ensures true;
{
    //@ open set(set);
    //@ open set_atomic(set, values);
    //@ assert set_nodesList(set, ?nodesList);
    //@ assert set_lockCounter(set, ?lockCounter);
    //@ ghost_counter_match_zero_contrib();
    //@ assert lseg(_, _, _, ?last, _, _, _, _);
    struct node *x = set->head;
    while (x->value < INT_MAX)
        /*@
        invariant
            lseg(nodesList, x, _, last, INT_MAX, _, _, 0) &*& (x == last ? true : true) &*&
            [1/2]x->value |-> ?xValue &*& [1/2]last->value |-> INT_MAX;
        @*/
    {
        //@ open lseg(_, _, _, _, _, _, _, _);
        //@ assert [1/2]node_lock(x, ?lockValue);
        struct node *y = x->next;
        free(x);
        //@ leak ghost_list_member_handle(nodesList, x);
        //@ open node_frac(x, _);
        x = y;
    }
    //@ open lseg(_, _, _, _, _, _, _, _);
    free(x);
    free(set);
    //@ leak ghost_list(nodesList, _);
    //@ leak ghost_counter_zero_contrib(_);
    //@ leak ghost_counter(_, _);
}

struct node *locate(struct set *set, int e)
    /*@
    requires
        INT_MIN < e &*&
        [?fSet]set->head |-> ?head &*&
        [fSet]set->nodesList |-> ?nodesList &*&
        [fSet]set->lockCounter |-> ?lockCounter &*&
        [?fContrib]ghost_counter_zero_contrib(lockCounter) &*&
        [?f]atomic_space(?inv) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep);
    @*/
    /*@
    ensures
        [fSet]set->head |-> head &*&
        [fSet]set->nodesList |-> nodesList &*&
        [fSet]set->lockCounter |-> lockCounter &*&
        ghost_counter_contrib(lockCounter, fContrib, 1) &*&
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
            [fSet]set->lockCounter |-> lockCounter &*&
            [fContrib]ghost_counter_zero_contrib(lockCounter) &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep);
        predicate_family_instance lock_context_post(context)() =
            [fSet]set->head |-> head &*&
            [fSet]set->nodesList |-> nodesList &*&
            [fSet]set->lockCounter |-> lockCounter &*&
            ghost_counter_contrib(lockCounter, fContrib, 1) &*&
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
            open lseg(nodesList, head, INT_MIN, ?last, INT_MAX, ?nodes, ?values_, ?lockCount);
            open [?fPointer]node_lock(head, _);
            op();
            assert [1/2]pointer(&head->lock, ?lockValue);
            close [fPointer]node_lock(head, lockValue);
            assert lock_operation_post(op)(?success);
            if (success) {
                open node_frac(head, 1);
                close node_frac(head, 1/2);
                close lseg(nodesList, head, INT_MIN, last, INT_MAX, nodes, values_, lockCount + 1);
                ghost_counter_start_contrib();
                ghost_counter_increment();
                close set_atomic(set, values);
                unsep();
                close lock_context_post(context)();
            } else {
                close lseg(nodesList, head, INT_MIN, last, INT_MAX, nodes, values_, lockCount);
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
        [fSet]set->lockCounter |-> lockCounter &*&
        ghost_counter_contrib(lockCounter, fContrib, 1) &*&
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
    if (c->value < e) {
        {
            /*@
            predicate_family_instance lock_context_pre(context)(predicate() inv_, void **lock) =
                inv_ == inv &*& lock == &c->lock &*&
                [fSet]set->head |-> head &*&
                [fSet]set->nodesList |-> nodesList &*&
                [fSet]set->lockCounter |-> lockCounter &*&
                ghost_counter_contrib(lockCounter, fContrib, 1) &*&
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
                [fSet]set->lockCounter |-> lockCounter &*&
                ghost_counter_contrib(lockCounter, fContrib, 2) &*&
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
                ghost_list_member_handle_lemma();
                lseg_split(p);
                open lseg(nodesList, p, ?pValue0, ?last, INT_MAX, ?nodes1, ?values1, ?lockCount1);
                open lseg(nodesList, c, ?cValue, last, INT_MAX, ?nodes2, ?values2, ?lockCount2);
                open node_lock(c, _);
                op();
                assert [?fPointer]pointer(&c->lock, ?lockValue);
                close [fPointer]node_lock(c, lockValue);
                assert lock_operation_post(op)(?success);
                if (success) {
                    open node_frac(c, 1);
                    close node_frac(c, 1/2);
                    close lseg(nodesList, c, cValue, last, INT_MAX, nodes2, values2, lockCount2 + 1);
                    close lseg(nodesList, p, pValue0, last, INT_MAX, nodes1, values1, lockCount1 + 1);
                    lseg_merge(p);
                    ghost_counter_increment();
                    close set_atomic(set, values);
                    unsep();
                    close lock_context_post(context)();
                } else {
                    close lseg(nodesList, c, cValue, last, INT_MAX, nodes2, values2, lockCount2);
                    close lseg(nodesList, p, pValue0, last, INT_MAX, nodes1, values1, lockCount1);
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
                [fSet]set->lockCounter |-> lockCounter &*&
                ghost_counter_contrib(lockCounter, fContrib, 2) &*&
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
                [fSet]set->lockCounter |-> lockCounter &*&
                ghost_counter_contrib(lockCounter, fContrib, 1) &*&
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
                ghost_list_member_handle_lemma();
                lseg_split(p);
                open lseg(nodesList, p, _, ?last, INT_MAX, ?nodes1, ?values1, ?lockCount1);
                open node_lock(p, _);
                op();
                close node_lock(p, 0);
                open node_frac(p, 1/2);
                close node_frac(p, 1);
                close lseg(nodesList, p, pValue, last, INT_MAX, nodes1, values1, lockCount1 - 1);
                lseg_merge(p);
                ghost_counter_decrement();
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

bool contains(struct set *set, int e)
    /*@
    requires
        INT_MIN < e &*& e < INT_MAX &*&
        [?f]atomic_space(?inv) &*&
        [?fSet]set(set) &*&
        is_set_sep(?sep) &*& is_set_unsep(?unsep) &*& set_sep(sep)(?info, set, inv, unsep) &*&
        is_set_contains(?op) &*& set_contains_pre(op)(unsep, info, e);
    @*/
    /*@
    ensures
        [f]atomic_space(inv) &*&
        [fSet]set(set) &*&
        is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
        is_set_contains(op) &*& set_contains_post(op)(result);
    @*/
{
    //@ open set(set);
    //@ assert [fSet/2]set->nodesList |-> ?nodesList;
    //@ assert [fSet/2]set->lockCounter |-> ?lockCounter;
    struct node *head = set->head;
    struct node *x = locate(set, e);
    struct node *z = x->next;
    bool result = z->value == e;
    //@ assert [1/4]x->value |-> ?xValue;
    //@ assert [1/4]z->value |-> ?zValue;
    {
        /*@
        predicate_family_instance atomic_store_pointer_context_pre(context)(predicate() inv_, void **pp, void *p_) =
            inv_ == inv &*& pp == &x->lock &*& p_ == 0 &*&
            [fSet/2]set->head |-> head &*&
            [fSet/2]set->nodesList |-> nodesList &*&
            [fSet/2]set->lockCounter |-> lockCounter &*&
            ghost_counter_contrib(lockCounter, fSet, 1) &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
            is_set_contains(op) &*& set_contains_pre(op)(unsep, info, e) &*&
            ghost_list_member_handle(nodesList, x) &*&
            [1/2]x->lock |-> (void *)1 &*&
            [1/2]x->oldNext |-> z &*&
            [1/4]x->value |-> xValue &*&
            [1/4]z->value |-> zValue &*&
            x->next |-> z;
        predicate_family_instance atomic_store_pointer_context_post(context)() =
            [fSet/2]set->head |-> head &*&
            [fSet/2]set->nodesList |-> nodesList &*&
            [fSet/2]set->lockCounter |-> lockCounter &*&
            [fSet]ghost_counter_zero_contrib(lockCounter) &*&
            is_set_sep(sep) &*& is_set_unsep(unsep) &*& set_sep(sep)(info, set, inv, unsep) &*&
            is_set_contains(op) &*& set_contains_post(op)(zValue == e);
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
            ghost_list_member_handle_lemma();
            lseg_split(x);
            assert lseg(nodesList, head, _, x, _, ?nodes0, ?values0, ?lockCount0);
            open lseg(nodesList, x, _, ?last, INT_MAX, ?nodes1, ?values1, ?lockCount1);
            open node_lock(x, _);
            sop();
            close node_lock(x, 0);
            open lseg(nodesList, z, zValue, last, INT_MAX, ?nodes2, ?values2, ?lockCount2);
            close lseg(nodesList, z, zValue, last, INT_MAX, nodes2, values2, lockCount2);
            open node_frac(x, 1/2);
            close node_frac(x, 1);
            close lseg(nodesList, x, xValue, last, INT_MAX, nodes1, values1, lockCount2);
            lseg_merge1(x, e);
            ghost_counter_decrement();
            ghost_counter_end_contrib();
            close set_atomic(set, values);
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

bool add(struct set *set, int e)
    /*@
    requires
        INT_MIN < e &*& e < INT_MAX &*&
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
    //@ assert [fSet/2]set->nodesList |-> ?nodesList;
    //@ assert [fSet/2]set->lockCounter |-> ?lockCounter;
    struct node *head = set->head;
    struct node *x = locate(set, e);
    struct node *z = x->next;
    bool result = false;
    struct node *y = 0;
    //@ assert [1/4]x->value |-> ?xValue;
    //@ assert [1/4]z->value |-> ?zValue;
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
            [fSet/2]set->lockCounter |-> lockCounter &*&
            ghost_counter_contrib(lockCounter, fSet, 1) &*&
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
            [fSet/2]set->lockCounter |-> lockCounter &*&
            [fSet]ghost_counter_zero_contrib(lockCounter) &*&
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
            ghost_list_member_handle_lemma();
            lseg_split(x);
            assert lseg(nodesList, head, _, x, _, ?nodes0, ?values0, ?lockCount0);
            open lseg(nodesList, x, _, ?last, INT_MAX, ?nodes1, ?values1, ?lockCount1);
            open node_lock(x, _);
            sop();
            close node_lock(x, 0);
            open lseg(nodesList, z, zValue, last, INT_MAX, ?nodes2, ?values2, ?lockCount2);
            close lseg(nodesList, z, zValue, last, INT_MAX, nodes2, values2, lockCount2);
            if (zValue != e) {
                x->oldNext = y;
                split_fraction node_value(y, _);
                append_assoc(nodes0, cons(x, nil), tail(nodes1));
                ghost_list_insert(nodesList, append(nodes0, cons(x, nil)), tail(nodes1), y);
                append_assoc(nodes0, cons(x, nil), cons(y, tail(nodes1)));
                close node_frac(y, 1);
                close lseg(nodesList, y, e, last, INT_MAX, cons(y, tail(nodes1)), cons(e, tail(values1)), lockCount2);
                open node_frac(x, 1/2);
                close node_frac(x, 1);
                close lseg(nodesList, x, xValue, last, INT_MAX, cons(x, cons(y, tail(nodes1))), cons(xValue, cons(e, tail(values1))), lockCount2);
                lseg_merge2(x, e, values1);
            } else {
                open node_frac(x, 1/2);
                close node_frac(x, 1);
                close lseg(nodesList, x, xValue, last, INT_MAX, nodes1, values1, lockCount2);
                lseg_merge2(x, e, values1);
            }
            ghost_counter_decrement();
            ghost_counter_end_contrib();
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
        INT_MIN < e &*& e < INT_MAX &*&
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
    //@ assert [fSet/2]set->lockCounter |-> ?lockCounter;
    struct node *head = set->head;
    struct node *x = locate(set, e);
    //@ assert [1/4]x->value |-> ?xValue;
    struct node *y = x->next;
    //@ assert [1/4]y->value |-> ?yValue;
    bool result = y->value == e;
    if (result) {
        {
            /*@
            predicate_family_instance lock_context_pre(context)(predicate() inv_, void **lock) =
                inv_ == inv &*& lock == &y->lock &*&
                [fSet/2]set->head |-> head &*&
                [fSet/2]set->nodesList |-> nodesList &*&
                [fSet/2]set->lockCounter |-> lockCounter &*&
                ghost_counter_contrib(lockCounter, fSet, 1) &*&
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
                [fSet/2]set->lockCounter |-> lockCounter &*&
                ghost_counter_contrib(lockCounter, fSet, 1) &*&
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
                ghost_list_member_handle_lemma();
                lseg_split(x);
                open lseg(nodesList, x, _, ?last, INT_MAX, ?nodes1, ?values1, ?lockCount1);
                assert lseg(nodesList, _, _, x, _, ?nodes0, ?values0, ?lockCount0);
                open lseg(nodesList, y, _, last, INT_MAX, ?nodes2, ?values2, ?lockCount2);
                open node_lock(y, _);
                lop();
                assert [?fPointer]pointer(&y->lock, ?lockValue);
                close [fPointer]node_lock(y, lockValue);
                assert lock_operation_post(lop)(?success);
                if (success) {
                    open node_frac(y, _);
                    struct node *z = y->oldNext;
                    x->oldNext = z;
                    close lseg(nodesList, x, xValue, last, INT_MAX, cons(x, tail(nodes2)), cons(xValue, tail(values2)), lockCount1);
                    lseg_merge3(x, e, values1);
                    append_assoc(nodes0, cons(x, nil), nodes2);
                    ghost_list_remove(nodesList, append(nodes0, cons(x, nil)), tail(nodes2), y);
                    append_assoc(nodes0, cons(x, nil), tail(nodes2));
                    close set_atomic(set, remove_sorted(e, values));
                    op();
                    unsep();
                    close lock_context_post(context)();
                } else {
                    close lseg(nodesList, y, yValue, last, INT_MAX, nodes2, values2, lockCount2);
                    close lseg(nodesList, x, xValue, last, INT_MAX, nodes1, values1, lockCount1);
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
            [fSet/2]set->lockCounter |-> lockCounter &*&
            ghost_counter_contrib(lockCounter, fSet, 1) &*&
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
            [fSet/2]set->lockCounter |-> lockCounter &*&
            [fSet]ghost_counter_zero_contrib(lockCounter) &*&
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
            ghost_list_member_handle_lemma();
            lseg_split(x);
            open lseg(nodesList, x, _, ?last, INT_MAX, ?nodes1, ?values1, ?lockCount1);
            assert [_]node_oldNext(x, ?next);
            assert [_]node_value(next, ?nextValue);
            open node_lock(x, _);
            sop();
            close node_lock(x, 0);
            open lseg(nodesList, next, nextValue, last, INT_MAX, ?nodes2, ?values2, ?lockCount2);
            close lseg(nodesList, next, nextValue, last, INT_MAX, nodes2, values2, lockCount2);
            open node_frac(x, 1/2);
            close node_frac(x, 1);
            close lseg(nodesList, x, xValue, last, INT_MAX, nodes1, values1, lockCount1 - 1);
            if (result)
                lseg_merge(x);
            else {
                lseg_merge3(x, e, values1);
                op();
            }
            ghost_counter_decrement();
            ghost_counter_end_contrib();
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
