//@ #include "atomics.gh"
#include "threading_terminates.h"
//@ #include "ghost_lists.gh"
#include "stack.h"
//@ #include "../termination.gh"
#include <stdlib.h>

struct node {
    struct node *next;
    void *value;
};
typedef struct node *node;

struct stack {
    //@ predicate(void *) p;
    //@ int readsId;
    node head;
};

/*@

predicate call_perms(int thread, int count, list<void *> fs) =
    count == 0 ?
        true
    :
        0 < count &*&
        call_perm_level(thread, pair((pair_lt)(lt, lt), pair(0, 0)), fs) &*& call_perms(thread, count - 1, fs);

predicate nodes(node n, predicate(void *) p) =
    n == 0 ?
        true
    :
        [_]n->value |-> ?value &*& p(value) &*&
        [_]n->next |-> ?next &*& nodes(next, p);

predicate node_ptr(node n) = n == 0 ? true : [_]n->next |-> ?_;

lemma void nodes_head_ptr()
    requires nodes(?n, ?p);
    ensures nodes(n, p) &*& [_]node_ptr(n);
{
    open nodes(n, p);
    close node_ptr(n);
    close nodes(n, p);
    leak node_ptr(n);
}

lemma void node_ptr_same_address(node n1, node n2)
    requires [_]node_ptr(n1) &*& [_]node_ptr(n2) &*& (uintptr_t)n1 == (uintptr_t)n2;
    ensures n1 == n2;
{
    open node_ptr(n1);
    open node_ptr(n2);
    if (n1 == 0) {
        if (n2 != 0)
            pointer_limits(&n2->next);
    } else {
        if (n2 == 0)
            pointer_limits(&n1->next);
        else
            if (n1 != n2)
                pointer_fractions_same_address(&n1->next, &n2->next);
    }
}

fixpoint bool neq<t>(t x, t y) { return x != y; }

predicate_ctor stack_space_inv(int scope, stack stack)() =
    stack->head |-> ?head &*&
    [_]stack->p |-> ?p &*&
    [_]stack->readsId |-> ?readsId &*&
    ghost_list<void *>(readsId, ?reads) &*& call_perms(?thread, count(reads, (neq)(head)), {stack_pop_iter}) &*& call_perm_scope_of(thread) == scope &*&
    nodes(head, p);

predicate stack(int scope, stack stack; predicate(void *) p) =
    [_]atomic_space(0, stack_space_inv(scope, stack)) &*&
    [_]stack->p |-> p;

@*/

stack create_stack()
    //@ requires exists<predicate(void *)>(?p);
    //@ ensures [_]stack(call_perm_scope_of(currentThread), result, p); 
    //@ terminates;
{
    //@ open exists(p);
    stack stack = malloc(sizeof(struct stack));
    if (stack == 0) abort();
    //@ stack->p = p;
    //@ int readsId = create_ghost_list<void *>();
    //@ close call_perms(currentThread, 0, {stack_pop_iter});
    //@ stack->readsId = readsId;
    stack->head = 0;
    //@ leak stack->p |-> p &*& stack->readsId |-> readsId &*& malloc_block_stack(stack);
    //@ close nodes(0, p);
    //@ close stack_space_inv(call_perm_scope_of(currentThread), stack)();
    //@ create_atomic_space(0, stack_space_inv(call_perm_scope_of(currentThread), stack));
    //@ leak atomic_space(0, stack_space_inv(call_perm_scope_of(currentThread), stack));
    //@ close stack(call_perm_scope_of(currentThread), stack, p);
    //@ leak stack(call_perm_scope_of(currentThread), stack, p);
    return stack;
}

/*@

lemma void consume_call_perm_level_for_<t>(pair<fixpoint(t, t, bool), t> level, list<void *> fs, void *f)
    requires call_perm_level<t>(?thread, level, fs) &*& mem(f, fs) == true;
    ensures call_perm_(thread, f);
{
    consume_call_perm_level_for(f);
}

@*/

void stack_push_iter(stack stack, void *value)
    //@ requires [_]stack(call_perm_scope_of(currentThread), stack, ?p) &*& p(value) &*& call_perm_level(currentThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
    //@ ensures true;
    //@ terminates;
{
    //@ int scope = call_perm_scope_of(currentThread);
    node n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->value = value;
    //@ leak n->value |-> value &*& malloc_block_node(n);
    for (;;)
        /*@
        invariant
            [_]stack(scope, stack, p) &*& p(value) &*& call_perm_level(currentThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter}) &*&
            [_]n->value |-> value &*& n->next |-> _;
        @*/
    {
        //@ open stack(scope, stack, p);
        node head;
        {
            /*@
            predicate P() = true;
            predicate Q(void *head_) = [_]stack->readsId |-> ?readsId &*& ghost_list_member_handle(readsId, head_) &*& [_]node_ptr(head_);
            lemma void ctxt()
                requires stack_space_inv(scope, stack)() &*& P() &*& is_atomic_load_op(?op, &stack->head, ?pre, ?post) &*& pre();
                ensures stack_space_inv(scope, stack)() &*& post(?head_) &*& Q(head_) &*& is_atomic_load_op(op, &stack->head, pre, post);
            {
                open stack_space_inv(scope, stack)();
                open P();

                nodes_head_ptr();
                node head_ = op();
                int readsId = stack->readsId;

                assert ghost_list(readsId, ?reads);
                ghost_list_insert(readsId, nil, reads, head_);

                close Q(head_);
                close stack_space_inv(scope, stack)();
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(ctxt) : atomic_load_ctxt(0, stack_space_inv(scope, stack), &stack->head, P, Q)() { call(); };
            //@ close P();
            head = atomic_load(&stack->head);
            //@ open Q(head);
        }
        n->next = head;
        //@ int readsId = stack->readsId;
        //@ int pushThread = currentThread;
        node head1;
        {
            /*@
            predicate P() =
                [_]stack->readsId |-> readsId &*& [_]stack->p |-> p &*& ghost_list_member_handle(readsId, head) &*&
                [_]n->value |-> value &*& p(value) &*& n->next |-> head &*&
                call_perm_level(pushThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
            predicate Q(void *head1_) =
                [_]node_ptr(head1_) &*&
                head1_ == head ?
                    true
                :
                    call_perm_(pushThread, stack_push_iter) &*&
                    p(value) &*& n->next |-> _ &*&
                    call_perm_level(pushThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
            lemma void ctxt()
                requires stack_space_inv(scope, stack)() &*& P() &*& is_atomic_compare_and_swap_op(?op, &stack->head, head, n, ?pre, ?post) &*& pre();
                ensures stack_space_inv(scope, stack)() &*& post(?head1_) &*& Q(head1_) &*& is_atomic_compare_and_swap_op(op, &stack->head, head, n, pre, post);
            {
                open stack_space_inv(scope, stack)();
                open P();

                node head0 = stack->head;
                nodes_head_ptr();
                assert ghost_list(readsId, ?reads);
                op();

		ghost_list_match();
                mem_remove_eq_append(head, reads);
                open exists(pair(?reads1_, ?reads2_));
                ghost_list_remove(readsId, reads1_, reads2_, head);
                assert ghost_list(readsId, ?reads1);

                if (head0 == head) {
                    leak n->next |-> head;
                    close nodes(n, p);
                    leak call_perms(_, count(reads, (neq)(head0)), {stack_pop_iter});
                    int m = count(reads1, (neq)(n));
                    count_nonnegative(reads1, (neq)(n));
                    is_wf_lt();
                    is_wf_pair_lt(lt, lt);
                    call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(1, 0), {stack_pop_iter}, 1, pair(0, m));
                    close call_perms(pushThread, 0, {stack_pop_iter});
                    for (int i = 0; i < m; i++)
                        invariant 0 <= i &*& i <= m &*& call_perms(pushThread, i, {stack_pop_iter}) &*& call_perm_level(pushThread, pair((pair_lt)(lt, lt), pair(0, m - i)), {stack_pop_iter});
                        decreases m - i;
                    {
                        is_wf_lt();
                        is_wf_pair_lt(lt, lt);
                        call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(0, m - i), {stack_pop_iter}, 2, pair(0, m - i - 1));
                        if (m - i - 1 != 0)
                            call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(0, m - i - 1), {stack_pop_iter}, 1, pair(0, 0));
                        close call_perms(pushThread, i + 1, {stack_pop_iter});
                    }
                    leak call_perm_level(_, _, _);
                } else {
                    count_append(reads1_, cons(head, reads2_), (neq)(head0));
                    assert count(cons(head, reads2_), (neq)(head0)) == count(reads2_, (neq)(head0)) + 1;
                    assert reads1 == append(reads1_, reads2_);
                    count_append(reads1_, reads2_, (neq)(head0));
                    assert count(reads1, (neq)(head0)) == count(reads, (neq)(head0)) - 1;
                    count_nonnegative(reads1, (neq)(head0));
                    open call_perms(?thread, _, _);
                    call_perm_level_below(1, pair((pair_lt)(lt, lt), pair(0, 0)), {stack_pop_iter}, 1);
                    consume_call_perm_for(stack_push_iter);
                    call_perm__transfer(pushThread);
                }

                close Q(head0);
                close stack_space_inv(scope, stack)();
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(ctxt) : atomic_compare_and_swap_ctxt(0, stack_space_inv(scope, stack), &stack->head, head, n, P, Q)() { call(); };
            //@ close P();
            head1 = atomic_compare_and_swap(&stack->head, head, n);
            //@ open Q(head1);
        }
        if (head1 == head) {
            //@ node_ptr_same_address(head1, head);
            break;
        }
    }
}

bool stack_pop_iter(stack stack, void **pvalue)
    //@ requires [_]stack(call_perm_scope_of(currentThread), stack, ?p) &*& *pvalue |-> _ &*& call_perm_(currentThread, stack_pop_iter) &*& call_perm_level(currentThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
    //@ ensures pointer_(pvalue, ?value_opt) &*& result ? value_opt == some(?value) &*& p(value) : true;
    //@ terminates;
{
    //@ int scope = call_perm_scope_of(currentThread);
    //@ int popThread = currentThread;
loop:
        /*@
        invariant
            [_]stack(scope, stack, p) &*& *pvalue |-> _ &*& call_perm_level(popThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
        @*/
    {
        //@ open stack(scope, stack, p);
        node head;
        {
            /*@
            predicate P() = true;
            predicate Q(node head_) =
                [_]stack->readsId |-> ?readsId &*& [_]node_ptr(head_) &*&
                head_ == 0 ? true : ghost_list_member_handle(readsId, head_) &*& [_]head_->next |-> ?next;
            lemma void ctxt()
                requires stack_space_inv(scope, stack)() &*& P() &*& is_atomic_load_op(?op, &stack->head, ?pre, ?post) &*& pre();
                ensures stack_space_inv(scope, stack)() &*& post(?head_) &*& Q(head_) &*& is_atomic_load_op(op, &stack->head, pre, post);
            {
                open stack_space_inv(scope, stack)();
                open P();
                
                nodes_head_ptr();

                node head_ = op();

                int readsId = stack->readsId;
                assert ghost_list(readsId, ?reads);
                
                if (head_ != 0) {
                    ghost_list_insert(readsId, nil, reads, head_);
                    open nodes(head_, ?p_);
                    close nodes(head_, p_);
                }

                close Q(head_);
                close stack_space_inv(scope, stack)();
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(ctxt) : atomic_load_ctxt(0, stack_space_inv(scope, stack), &stack->head, P, Q)() { call(); };
            //@ close P();
            head = atomic_load(&stack->head);
            //@ open Q(head);
        }
        //@ int readsId = stack->readsId;
        if (head == 0) {
            //@ leak call_perm_level(popThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
            return false;
        }
        node next = head->next;
        node head0;
        {
            /*@
            predicate P() =
                [_]stack->readsId |-> readsId &*& [_]stack->p |-> p &*& ghost_list_member_handle(readsId, head) &*&
                [_]head->next |-> next &*&
                call_perm_level(popThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
            predicate Q(void *head1) =
                [_]node_ptr(head1) &*&
                head1 == head ?
                    [_]head->value |-> ?value &*& p(value)
                :
                    call_perm_(popThread, stack_pop_iter) &*&
                    call_perm_level(popThread, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
            lemma void ctxt()
                requires stack_space_inv(scope, stack)() &*& P() &*& is_atomic_compare_and_swap_op(?op, &stack->head, head, next, ?pre, ?post) &*& pre();
                ensures stack_space_inv(scope, stack)() &*& post(?head1) &*& Q(head1) &*& is_atomic_compare_and_swap_op(op, &stack->head, head, next, pre, post);
            {
                open stack_space_inv(scope, stack)();
                open P();
                
                nodes_head_ptr();

                node head0_ = stack->head;
                assert ghost_list(readsId, ?reads);
                op();

                ghost_list_match();
                mem_remove_eq_append(head, reads);
                open exists(pair(?reads1_, ?reads2_));
                ghost_list_remove(readsId, reads1_, reads2_, head);
                assert ghost_list(readsId, ?reads1);

                if (head0_ == head) {
                    open nodes(head, p);
                    leak call_perms(_, count(reads, (neq)(head0_)), {stack_pop_iter});
                    int n = count(reads1, (neq)(next));
                    count_nonnegative(reads1, (neq)(next));
                    is_wf_lt();
                    is_wf_pair_lt(lt, lt);
                    call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(1, 0), {stack_pop_iter}, 1, pair(0, n));
                    close call_perms(popThread, 0, {stack_pop_iter});
                    for (int i = 0; i < n; i++)
                        invariant 0 <= i &*& i <= n &*& call_perms(popThread, i, {stack_pop_iter}) &*& call_perm_level(popThread, pair((pair_lt)(lt, lt), pair(0, n - i)), {stack_pop_iter});
                        decreases n - i;
                    {
                        is_wf_lt();
                        is_wf_pair_lt(lt, lt);
                        call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(0, n - i), {stack_pop_iter}, 2, pair(0, n - i - 1));
                        if (n - i - 1 != 0)
                            call_perm_level_weaken(1, (pair_lt)(lt, lt), pair(0, n - i - 1), {stack_pop_iter}, 1, pair(0, 0));
                        close call_perms(popThread, i + 1, {stack_pop_iter});
                    }
                    leak call_perm_level(_, pair((pair_lt)(lt, lt), pair(0, 0)), {stack_pop_iter});
                } else {
                    count_append(reads1_, cons(head, reads2_), (neq)(head0_));
                    count_append(reads1_, reads2_, (neq)(head0_));
                    assert count(reads1, (neq)(head0_)) == count(reads, (neq)(head0_)) - 1;
                    count_nonnegative(reads1, (neq)(head0_));
                    open call_perms(?thread, _, _);
                    consume_call_perm_level_for_(pair((pair_lt)(lt, lt), pair(0, 0)), {stack_pop_iter}, stack_pop_iter);
                    call_perm__transfer(popThread);
                }

                close Q(head0_);
                close stack_space_inv(scope, stack)();
            }
            @*/
            //@ produce_lemma_function_pointer_chunk(ctxt) : atomic_compare_and_swap_ctxt(0, stack_space_inv(scope, stack), &stack->head, head, next, P, Q)() { call(); };
            //@ close P();
            head0 = atomic_compare_and_swap(&stack->head, head, next);
            //@ open Q(head0);
        }
        if (head0 == head) {
            //@ node_ptr_same_address(head0, head);
            *pvalue = head->value;
            return true;
        }
        goto loop;
    }
}

void stack_push(stack stack, void *value)
    //@ requires [_]stack(call_perm_scope_of(currentThread), stack, ?p) &*& p(value);
    //@ ensures true;
    //@ terminates;
{
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(stack_push);
    //@ call_perm_level(1, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
    stack_push_iter(stack, value);
}

bool stack_pop(stack stack, void **pvalue)
    //@ requires [_]stack(call_perm_scope_of(currentThread), stack, ?p) &*& *pvalue |-> _;
    //@ ensures pointer_(pvalue, ?value_opt) &*& result ? value_opt == some(?value) &*& p(value) : true;
    //@ terminates;
{
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(stack_pop);
    //@ consume_call_perm_for(stack_pop_iter);
    //@ produce_call_below_perm_();
    //@ call_below_perm__elim(stack_pop);
    //@ call_perm_level(1, pair((pair_lt)(lt, lt), pair(1, 0)), {stack_pop_iter});
    return stack_pop_iter(stack, pvalue);
}

#endif
