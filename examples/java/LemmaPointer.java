class Cell {
    int value;
}

/*@

inductive IncrementingRunnable_info = IncrementingRunnable_info(Cell c, int value);

predicate_family IncrementingRunnable(Class c)(Runnable r, Cell c);

typedef lemma void IncrementingRunnable_to_Runnable(Runnable r)();
    requires IncrementingRunnable(r.getClass())(r, ?c) &*& c.value |-> ?value;
    ensures thread_run_pre(r.getClass())(r, IncrementingRunnable_info(c, value));

typedef lemma void Runnable_to_IncrementingRunnable(Runnable r)(Cell c, int value);
    requires thread_run_post(r.getClass())(r, IncrementingRunnable_info(c, value));
    ensures IncrementingRunnable(r.getClass())(r, c) &*& c.value |-> value + 1;

@*/

class IncrementingRunnableTester {
    static void test(Cell c, Runnable r)
        /*@
        requires
            c.value |-> ?value &*& r != null &*&
            IncrementingRunnable(r.getClass())(r, c) &*&
            is_IncrementingRunnable_to_Runnable(?lemmaPointer1, r) &*&
            is_Runnable_to_IncrementingRunnable(?lemmaPointer2, r);
        @*/
        //@ ensures true;
    {
        int v1 = c.value;
        //@ lemmaPointer1();
        r.run();
        //@ lemmaPointer2(c, v1);
        int v2 = c.value;
        assert(v2 == v1 + 1);
    }
}

/*@

predicate_family_instance IncrementingRunnable(MyRunnable.class)(MyRunnable r, Cell c) = r.c |-> c;

predicate_family_instance thread_run_pre(MyRunnable.class)(MyRunnable r, IncrementingRunnable_info info) =
    switch (info) {
        case IncrementingRunnable_info(c, value): return r.c |-> c &*& c.value |-> value;
    };

predicate_family_instance thread_run_post(MyRunnable.class)(MyRunnable r, IncrementingRunnable_info info) =
    switch (info) {
        case IncrementingRunnable_info(c, value): return r.c |-> c &*& c.value |-> value + 1;
    };

lemma void IncrementingRunnable_to_MyRunnable()
    requires IncrementingRunnable(MyRunnable.class)(?r, ?c) &*& c.value |-> ?value;
    ensures thread_run_pre(MyRunnable.class)(r, IncrementingRunnable_info(c, value));
{
    open IncrementingRunnable(MyRunnable.class)(?r_, c);
    close thread_run_pre(MyRunnable.class)(r_, IncrementingRunnable_info(c, value));
}

lemma void MyRunnable_to_IncrementingRunnable(Cell c, int value)
    requires thread_run_post(MyRunnable.class)(?r, IncrementingRunnable_info(c, value));
    ensures IncrementingRunnable(MyRunnable.class)(r, c) &*& c.value |-> value + 1;
{
    open thread_run_post(MyRunnable.class)(?r_, _);
    close IncrementingRunnable(MyRunnable.class)(r_, c);
}

@*/

final class MyRunnable implements Runnable {
    Cell c;

    public void run()
    {
        //@ open thread_run_pre(MyRunnable.class)(this, ?info_);
        c.value++;
        //@ close thread_run_post(MyRunnable.class)(this, info_);
    }

    static void test()
        //@ requires true;
        //@ ensures true;
    {
        Cell c = new Cell();
        MyRunnable r = new MyRunnable();
        r.c = c;
        //@ close IncrementingRunnable(MyRunnable.class)(r, c);
        //@ produce_lemma_function_pointer_chunk(IncrementingRunnable_to_MyRunnable) : IncrementingRunnable_to_Runnable(r)() { call(); };
        //@ produce_lemma_function_pointer_chunk(MyRunnable_to_IncrementingRunnable) : Runnable_to_IncrementingRunnable(r)(c0, value0) { call(); };
        IncrementingRunnableTester.test(c, r);
    }
}

/*@

predicate_family_instance IncrementingRunnable(YourRunnable.class)(YourRunnable r, Cell c) = r.c |-> c;

predicate_family_instance thread_run_pre(YourRunnable.class)(YourRunnable r, IncrementingRunnable_info info) =
    switch (info) {
        case IncrementingRunnable_info(c, value): return r.c |-> c &*& c.value |-> value;
    };

predicate_family_instance thread_run_post(YourRunnable.class)(YourRunnable r, IncrementingRunnable_info info) =
    switch (info) {
        case IncrementingRunnable_info(c, value): return r.c |-> c &*& c.value |-> value + 1;
    };

lemma void IncrementingRunnable_to_YourRunnable()
    requires IncrementingRunnable(YourRunnable.class)(?r, ?c) &*& c.value |-> ?value;
    ensures thread_run_pre(YourRunnable.class)(r, IncrementingRunnable_info(c, value));
{
    open IncrementingRunnable(YourRunnable.class)(?r_, c);
    close thread_run_pre(YourRunnable.class)(r_, IncrementingRunnable_info(c, value));
}

lemma void YourRunnable_to_IncrementingRunnable(Cell c, int value)
    requires thread_run_post(YourRunnable.class)(?r, IncrementingRunnable_info(c, value));
    ensures IncrementingRunnable(YourRunnable.class)(r, c) &*& c.value |-> value + 1;
{
    open thread_run_post(YourRunnable.class)(?r_, _);
    close IncrementingRunnable(YourRunnable.class)(r_, c);
}

@*/

final class YourRunnable implements Runnable {
    Cell c;

    public void run()
    {
        //@ open thread_run_pre(YourRunnable.class)(this, ?info_);
        c.value++;
        //@ close thread_run_post(YourRunnable.class)(this, info_);
    }

    static void test()
        //@ requires true;
        //@ ensures true;
    {
        Cell c = new Cell();
        YourRunnable r = new YourRunnable();
        r.c = c;
        //@ close IncrementingRunnable(YourRunnable.class)(r, c);
        //@ produce_lemma_function_pointer_chunk(IncrementingRunnable_to_YourRunnable) : IncrementingRunnable_to_Runnable(r)() { call(); };
        //@ produce_lemma_function_pointer_chunk(YourRunnable_to_IncrementingRunnable) : Runnable_to_IncrementingRunnable(r)(c0, value0) { call(); };
        IncrementingRunnableTester.test(c, r);
    }
}
