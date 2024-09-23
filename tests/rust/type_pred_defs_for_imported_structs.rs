//@ pred_ctor my_fbc(t: thread_id_t, l: *std::io::Stdout)() = false;
//@ type_pred_def <std::io::Stdout>.full_borrow_content = my_fbc; //~should_fail
