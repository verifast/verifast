/*@

pred foo<T>(type_id: *_) = type_id == typeid(T);

lem noop<T>()
    req foo::<T>(?type_id);
    ens foo::<T>(type_id);
{}

lem lft_collapse<'a1, 'a2>()
    req true;
    ens typeid(&'a1 u8) == typeid(&'a2 u8);
{
    close foo::<&'a1 u8>(typeid(&'a1 u8));
    noop::<&'a2 u8>(); //~should_fail
    open foo::<&'a2 u8>(_); //~allow_dead_code
}

@*/
