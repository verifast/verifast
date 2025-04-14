/* Tests for VeriFast ghost command injection */
mod foo {
    mod bar {
        pub unsafe fn bar()
        //@ req true;
        //@ ens true;
        //@ on_unwind_ens true;
        {
            //@ assert true;
        }
    }
    pub unsafe fn foo()
    //@ req true;
    //@ ens true;
    //@ on_unwind_ens true;
    {
        //@ assert true;
    }
}
