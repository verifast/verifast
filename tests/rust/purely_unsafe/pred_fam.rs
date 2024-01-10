struct Foo;

struct Bar;

/*@

pred_fam quux(idx: *std::type_info)();

pred_fam_inst quux(typeid(Foo))() = true;
pred_fam_inst quux(typeid(Bar))() = false;

lem Foo_intro(idx: *std::type_info)
    req idx == typeid(Foo);
    ens quux(idx)();
{
    close quux(typeid(Foo))();
}

lem Bar_elim(idx: *std::type_info)
    req quux(idx)() &*& idx == typeid(Bar);
    ens false;
{
    open quux(typeid(Bar))();
}

@*/
