use std::cmp::Ordering;
//@ use std::cmp::Ordering;

unsafe fn reverse_ordering(o: Ordering) -> Ordering
//@ req true;
/*@
ens result == match o {
        Ordering::Less => Ordering::Greater,
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Less,
    };
@*/
{
    match o {
        Ordering::Less => Ordering::Greater,
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Less
    }
}
