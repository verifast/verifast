//@ #include "obspace_credit_objects.gh"

/*@

lemma int create_obspace_credit_object(int space, level level)
    nonghost_callers_only
    requires [?fs]obligation_space(space, ?termScope);
    ensures [fs]obligation_space(space, termScope) &*& obspace_credit_object(result, space, level, 0, 0);
{
    open [fs]obligation_space(space, termScope);
    assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    int creditObject = create_credit_object(scope, level);
    close credit_object_(creditObject, scope, level)();
    create_atomic_space(olevel + 1, credit_object_(creditObject, scope, level));
    leak atomic_space(olevel + 1, credit_object_(creditObject, scope, level));
    close obspace_credit_object(creditObject, space, level, 0, 0);
    close [fs]obligation_space(space, termScope);
    return creditObject;
}

lemma void obspace_credit_object_get_info()
    requires obspace_credit_object(?creditObject, ?space, ?level, ?items, ?blockees);
    ensures obspace_credit_object(creditObject, space, level, items, blockees) &*& [_]obspace_credit_object_info(creditObject, space, level);
{
    open obspace_credit_object(creditObject, space, level, items, blockees);
    close obspace_credit_object(creditObject, space, level, items, blockees);
    close obspace_credit_object_info(creditObject, space, level);
    leak obspace_credit_object_info(creditObject, space, level);
}

lemma void create_obspace_debit()
    nonghost_callers_only
    requires
        [_]obspace_credit_object_info(?creditObject, ?space, ?level) &*&
        [?fs]obligation_space(space, ?termScope) &*&
        obspace_obligation_set(space, ?obs);
    ensures
        [fs]obligation_space(space, termScope) &*&
        obspace_obligation_set(space, cons(level, obs)) &*&
        credit(creditObject) &*& debit(creditObject);
{
    open [_]obspace_credit_object_info(creditObject, space, level);
    open [fs]obligation_space(space, termScope);
    open obspace_obligation_set(space, obs);
    assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    {
        predicate P() = [fs]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*& obligation_set(scope, obs);
        predicate Q() = [fs]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*& obligation_set(scope, cons(level, obs)) &*& credit(creditObject) &*& debit(creditObject);
        lemma void body()
            requires atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& P();
            ensures atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& Q();
        {
            open credit_object_(creditObject, scope, level)();
            open P();

            {
                predicate P1() = obligation_set(scope, obs);
                predicate Q1() = obligation_set(scope, cons(level, obs)) &*& obligation(scope, level);
                lemma void body1()
                    requires obligation_space_inv(scope, termScope)() &*& P1();
                    ensures obligation_space_inv(scope, termScope)() &*& Q1();
                {
                    open obligation_space_inv(scope, termScope)();
                    open P1();
                    create_obligation(level);
                    close Q1();
                    close obligation_space_inv(scope, termScope)();
                }
                produce_lemma_function_pointer_chunk(body1) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }
            create_debit();

            close credit_object_(creditObject, scope, level)();
            close Q();
        }
        produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel + 1, credit_object_(creditObject, scope, level), P, Q)() { call(); } {
            close P();
            atomic_noop();
            open Q();
        }
    }

    close [fs]obligation_space(space, termScope);
    close obspace_obligation_set(space, cons(level, obs));
}

lemma void obspace_debit_dispose()
    nonghost_callers_only
    requires
        [_]obspace_credit_object_info(?creditObject, ?space, ?level) &*&
        [?fs]obligation_space(space, ?termScope) &*&
        obspace_obligation_set(space, ?obs) &*& mem(level, obs) == true &*&
        credit(creditObject) &*& debit(creditObject);
    ensures
        [fs]obligation_space(space, termScope) &*&
        obspace_obligation_set(space, remove(level, obs));
{
    open [_]obspace_credit_object_info(creditObject, space, level);
    open [fs]obligation_space(space, termScope);
    open obspace_obligation_set(space, obs);
    assert [_]ghost_cell<pair<int, real> >(space, pair(?scope, ?olevel));
    {
        predicate P() = [fs]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*& obligation_set(scope, obs) &*& credit(creditObject) &*& debit(creditObject);
        predicate Q() = [fs]atomic_space(olevel, obligation_space_inv(scope, termScope)) &*& obligation_set(scope, remove(level, obs));
        lemma void body()
            requires atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& P();
            ensures atomic_space_level(olevel + 1) &*& credit_object_(creditObject, scope, level)() &*& Q();
        {
            open credit_object_(creditObject, scope, level)();
            open P();

            debit_dispose();
            {
                predicate P1() = obligation_set(scope, obs) &*& obligation(scope, level);
                predicate Q1() = obligation_set(scope, remove(level, obs));
                lemma void body1()
                    requires obligation_space_inv(scope, termScope)() &*& P1();
                    ensures obligation_space_inv(scope, termScope)() &*& Q1();
                {
                    open obligation_space_inv(scope, termScope)();
                    open P1();
                    destroy_obligation();
                    close Q1();
                    close obligation_space_inv(scope, termScope)();
                }
                produce_lemma_function_pointer_chunk(body1) : atomic_noop_body(olevel, obligation_space_inv(scope, termScope), P1, Q1)() { call(); } {
                    close P1();
                    atomic_noop_nested();
                    open Q1();
                }
            }

            close credit_object_(creditObject, scope, level)();
            close Q();
        }
        produce_lemma_function_pointer_chunk(body) : atomic_noop_body(olevel + 1, credit_object_(creditObject, scope, level), P, Q)() { call(); } {
            close P();
            atomic_noop();
            open Q();
        }
    }

    close [fs]obligation_space(space, termScope);
    close obspace_obligation_set(space, remove(level, obs));
}

@*/
