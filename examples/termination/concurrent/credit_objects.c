//@ #include "credit_objects.gh"

/*@

predicate n_times(int n, predicate() p) =
    n == 0 ?
        true
    :
        p() &*& n_times(n - 1, p);

lemma_auto void n_times_inv()
    requires n_times(?n, ?p);
    ensures n_times(n, p) &*& 0 <= n;
{
    open n_times(_, _);
    if (n != 0)
        n_times_inv();
    close n_times(n, p);
}

predicate_ctor obligation_(int scope, level level)() = obligation(scope, level);

inductive ids = ids(int debitsId, int creditsId, int itemsId, int blockeesId);

predicate credit_object(int id, int scope, level level) =
    [_]ghost_cell<ids>(id, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId)) &*&
    [1/2]ghost_cell(itemsId, ?items) &*&
    [1/2]ghost_cell(blockeesId, ?blockees) &*&
    0 <= items &*& 0 <= blockees &*& items == 0 || blockees == 0 &*&
    ghost_counter(debitsId, ?debits) &*&
    ghost_counter(creditsId, items + debits - blockees) &*&
    n_times(debits - blockees, obligation_(scope, level));

predicate credit_object_handle(int id, int items, int blockees) =
    [_]ghost_cell<ids>(id, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId)) &*&
    [1/2]ghost_cell(itemsId, items) &*&
    [1/2]ghost_cell(blockeesId, blockees);

predicate credit(int creditObject;) =
    [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId)) &*&
    ghost_counter_ticket(creditsId);

predicate debit(int creditObject;) =
    [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId)) &*&
    ghost_counter_ticket(debitsId);

lemma int create_credit_object(int scope, level level)
    requires true;
    ensures credit_object(result, scope, level) &*& credit_object_handle(result, 0, 0);
{
    int debitsId = create_ghost_counter();
    int creditsId = create_ghost_counter();
    int itemsId = create_ghost_cell(0);
    int blockeesId = create_ghost_cell(0);
    close n_times(0, obligation_(scope, level));
    int result = create_ghost_cell(ids(debitsId, creditsId, itemsId, blockeesId));
    leak ghost_cell(_, _);
    close credit_object(result, scope, level);
    close credit_object_handle(result, 0, 0);
    return result;
}

lemma void create_debit()
    requires credit_object(?creditObject, ?scope, ?level) &*& obligation(scope, level);
    ensures credit_object(creditObject, scope, level) &*& credit(creditObject) &*& debit(creditObject);
{
    open credit_object(creditObject, scope, level);
    assert [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId));
    create_ghost_counter_ticket(debitsId);
    create_ghost_counter_ticket(creditsId);
    assert n_times(?debits, _);
    close obligation_(scope, level)();
    close n_times(debits + 1, obligation_(scope, level));
    close credit_object(creditObject, scope, level);
}

lemma void debit_dispose()
    requires credit_object(?creditObject, ?scope, ?level) &*& credit(creditObject) &*& debit(creditObject);
    ensures credit_object(creditObject, scope, level) &*& obligation(scope, level);
{
    open credit_object(creditObject, scope, level);
    assert [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId));
    open debit(_);
    ghost_counter_destroy_ticket(debitsId);
    open credit(_);
    ghost_counter_destroy_ticket(creditsId);
    open n_times(_, _);
    open obligation_(scope, level)();
    close credit_object(creditObject, scope, level);
}

lemma void credit_object_block()
    requires credit_object(?creditObject, ?scope, ?level) &*& credit_object_handle(creditObject, 0, ?blockees) &*& credit(creditObject);
    ensures credit_object(creditObject, scope, level) &*& credit_object_handle(creditObject, 0, blockees + 1) &*& obligation(scope, level);
{
    open credit_object(creditObject, scope, level);
    open credit_object_handle(creditObject, 0, blockees);
    assert [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId));
    open credit(_);
    ghost_counter_destroy_ticket(creditsId);
    open n_times(_, _);
    open obligation_(scope, level)();
    ghost_cell_mutate(blockeesId, blockees + 1);
    close credit_object(creditObject, scope, level);
    close credit_object_handle(creditObject, 0, blockees + 1);
}

lemma void credit_object_unblock()
    requires credit_object(?creditObject, ?scope, ?level) &*& credit_object_handle(creditObject, 0, ?blockees) &*& 0 < blockees &*& obligation(scope, level);
    ensures credit_object(creditObject, scope, level) &*& credit_object_handle(creditObject, 0, blockees - 1) &*& credit(creditObject);
{
    open credit_object(creditObject, scope, level);
    open credit_object_handle(creditObject, 0, blockees);
    assert [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId));
    create_ghost_counter_ticket(creditsId);
    ghost_cell_mutate(blockeesId, blockees - 1);
    assert n_times(?n, _);
    close obligation_(scope, level)();
    close n_times(n + 1, obligation_(scope, level));
    close credit_object(creditObject, scope, level);
    close credit_object_handle(creditObject, 0, blockees - 1);
}

lemma void credit_object_acquire()
    requires credit_object(?creditObject, ?scope, ?level) &*& credit_object_handle(creditObject, ?items, 0) &*& 0 < items &*& credit(creditObject);
    ensures credit_object(creditObject, scope, level) &*& credit_object_handle(creditObject, items - 1, 0);
{
    open credit_object(creditObject, scope, level);
    open credit_object_handle(creditObject, items, 0);
    assert [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId));
    open credit(_);
    ghost_counter_destroy_ticket(creditsId);
    ghost_cell_mutate(itemsId, items - 1);
    close credit_object(creditObject, scope, level);
    close credit_object_handle(creditObject, items - 1, 0);
}

lemma void credit_object_release()
    requires credit_object(?creditObject, ?scope, ?level) &*& credit_object_handle(creditObject, ?items, 0);
    ensures credit_object(creditObject, scope, level) &*& credit_object_handle(creditObject, items + 1, 0) &*& credit(creditObject);
{
    open credit_object(creditObject, scope, level);
    open credit_object_handle(creditObject, items, 0);
    assert [_]ghost_cell<ids>(creditObject, ids(?debitsId, ?creditsId, ?itemsId, ?blockeesId));
    create_ghost_counter_ticket(creditsId);
    ghost_cell_mutate(itemsId, items + 1);
    close credit_object(creditObject, scope, level);
    close credit_object_handle(creditObject, items + 1, 0);
}

@*/
