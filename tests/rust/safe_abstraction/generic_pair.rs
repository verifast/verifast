pub struct Pair<A, B> {
    fst: A,
    snd: B
}

/*@

pred Pair_own<A, B>(t: thread_id_t, fst: A, snd: B) = <A>.own(t, fst) &*& <B>.own(t, snd);

pred Pair_share<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>) =
    [_](<A>.share)(k, t, &(*l).fst) &*&
    pointer_within_limits(&(*l).snd) == true &*&
    [_](<B>.share)(k, t, &(*l).snd);

lem Pair_share_mono<A, B>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req type_interp::<A>() &*& type_interp::<B>() &*& lifetime_inclusion(k1, k) == true &*& [_]Pair_share::<A, B>(k, t, l);
    ens type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(k1, t, l);
{
    open Pair_share(k, t, l);
    share_mono::<A>(k, k1, t, &(*l).fst);
    share_mono::<B>(k, k1, t, &(*l).snd);
    close Pair_share(k1, t, l);
    leak Pair_share(k1, t, l);
}

pred_ctor struct_Pair_padding_<A, B>(l: *Pair<A, B>)() = struct_Pair_padding(l);

pred True(;) = true;

lem Pair_split_full_borrow_m<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req
        atomic_mask(?mask) &*& mask_le(Nlft, mask) == true &*&
        type_interp::<A>() &*& type_interp::<B>() &*&
        full_borrow(k, Pair_full_borrow_content::<A, B>(t, l)) &*& [?q]lifetime_token(k);
    ens
        atomic_mask(mask) &*& type_interp::<A>() &*& type_interp::<B>() &*&
        full_borrow(k, <A>.full_borrow_content(t, &(*l).fst)) &*&
        full_borrow(k, <B>.full_borrow_content(t, &(*l).snd)) &*&
        [q]lifetime_token(k) &*&
        pointer_within_limits(&(*l).snd) == true;
{
    let klong = open_full_borrow_strong_m(k, Pair_full_borrow_content::<A, B>(t, l), q);
    {
        open Pair_full_borrow_content::<A, B>(t, l)();
        open Pair_fst(l, _);
        open Pair_snd(l, _);
        open Pair_own(_, _, _);
        close struct_Pair_padding_::<A, B>(l)();
        close_full_borrow_content::<A>(t, &(*l).fst);
        close_full_borrow_content::<B>(t, &(*l).snd);
        close sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        close sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
    }
    produce_lem_ptr_chunk full_borrow_convert_strong(True, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))), klong, Pair_full_borrow_content::<A, B>(t, l))() {
        open sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
        open struct_Pair_padding_::<A, B>(l)();
        open sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        open_full_borrow_content(t, &(*l).fst);
        open_full_borrow_content(t, &(*l).snd);
        close Pair_fst(l, ?fst);
        close Pair_snd(l, ?snd);
        close Pair_own(t, fst, snd);
        close Pair_full_borrow_content::<A, B>(t, l)();
    } {
        close_full_borrow_strong_m(klong, Pair_full_borrow_content::<A, B>(t, l), sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    }
    full_borrow_mono(klong, k, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    full_borrow_split_m(k, struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)));
    full_borrow_split_m(k, <A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd));
    leak full_borrow(k, struct_Pair_padding_::<A, B>(l));
}

lem Pair_split_full_borrow<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>) // TODO: Eliminate this duplication.
    nonghost_callers_only
    req
        full_borrow(k, Pair_full_borrow_content::<A, B>(t, l)) &*& [?q]lifetime_token(k);
    ens
        full_borrow(k, <A>.full_borrow_content(t, &(*l).fst)) &*&
        full_borrow(k, <B>.full_borrow_content(t, &(*l).snd)) &*&
        [q]lifetime_token(k) &*&
        pointer_within_limits(&(*l).snd) == true;
{
    produce_type_interp::<A>();
    produce_type_interp::<B>();
    let klong = open_full_borrow_strong(k, Pair_full_borrow_content::<A, B>(t, l), q);
    {
        open Pair_full_borrow_content::<A, B>(t, l)();
        open Pair_fst(l, _);
        open Pair_snd(l, _);
        open Pair_own(_, _, _);
        close struct_Pair_padding_::<A, B>(l)();
        close_full_borrow_content::<A>(t, &(*l).fst);
        close_full_borrow_content::<B>(t, &(*l).snd);
        close sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        close sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
    }
    produce_lem_ptr_chunk full_borrow_convert_strong(True, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))), klong, Pair_full_borrow_content::<A, B>(t, l))() {
        open sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)))();
        open struct_Pair_padding_::<A, B>(l)();
        open sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))();
        open_full_borrow_content(t, &(*l).fst);
        open_full_borrow_content(t, &(*l).snd);
        close Pair_fst(l, ?fst);
        close Pair_snd(l, ?snd);
        close Pair_own(t, fst, snd);
        close Pair_full_borrow_content::<A, B>(t, l)();
    } {
        close_full_borrow_strong(klong, Pair_full_borrow_content::<A, B>(t, l), sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    }
    full_borrow_mono(klong, k, sep(struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd))));
    full_borrow_split(k, struct_Pair_padding_::<A, B>(l), sep(<A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd)));
    full_borrow_split(k, <A>.full_borrow_content(t, &(*l).fst), <B>.full_borrow_content(t, &(*l).snd));
    leak full_borrow(k, struct_Pair_padding_::<A, B>(l));
    leak type_interp() &*& type_interp();
}

lem Pair_share_full<A, B>(k: lifetime_t, t: thread_id_t, l: *Pair<A, B>)
    req atomic_mask(Nlft) &*& type_interp::<A>() &*& type_interp::<B>() &*& full_borrow(k, Pair_full_borrow_content::<A, B>(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& type_interp::<A>() &*& type_interp::<B>() &*& [_]Pair_share::<A, B>(k, t, l) &*& [q]lifetime_token(k);
{
    Pair_split_full_borrow_m(k, t, l);
    share_full_borrow_m::<A>(k, t, &(*l).fst);
    share_full_borrow_m::<B>(k, t, &(*l).snd);
    close Pair_share(k, t, l);
    leak Pair_share(k, t, l);
}

@*/

impl<A, B> Pair<A, B> {

    pub fn new(fst: A, snd: B) -> Self {
        //@ close Pair_own::<A, B>(_t, fst, snd);
        Pair { fst, snd }
    }

    pub fn get_fst_leak_snd(self) -> A {
        //@ open Pair_own::<A, B>(_t, self.fst, self.snd);
        let _snd = std::mem::ManuallyDrop::new(self.snd);
        //@ leak <B>.own(_t, self.snd);
        self.fst
    }

    pub fn get_fst_drop_snd(self) -> A {
        //@ open Pair_own::<A, B>(_t, self.fst, self.snd);
        std::mem::drop(self.snd);
        self.fst
    }

    pub fn get_snd_leak_fst(self) -> B {
        //@ open Pair_own::<A, B>(_t, self.fst, self.snd);
        let _fst = std::mem::ManuallyDrop::new(self.fst);
        //@ leak <A>.own(_t, self.fst);
        self.snd
    }
    
    pub fn get_snd_drop_fst(self) -> B {
        //@ open Pair_own::<A, B>(_t, self.fst, self.snd);
        std::mem::drop(self.fst);
        self.snd
    }
    
    pub fn deref_fst<'a>(&'a self) -> &'a A {
        //@ open Pair_share::<A, B>('a, _t, self);
        &self.fst
    }
    
    pub fn deref_snd<'a>(&'a self) -> &'a B {
        //@ open Pair_share::<A, B>('a, _t, self);
        &self.snd
    }
    
    pub fn replace_fst<'a>(&'a mut self, new_fst: A) -> A {
        unsafe {
            //@ open_full_borrow(_q_a, 'a, Pair_full_borrow_content::<A, B>(_t, self));
            //@ open Pair_full_borrow_content::<A, B>(_t, self)();
            //@ open Pair_own(_t, ?fst0, ?snd0);
            //@ open Pair_fst(self, fst0);
            let result = std::ptr::read(&self.fst);
            std::ptr::write(&mut self.fst, new_fst);
            //@ close Pair_fst(self, new_fst);
            //@ close Pair_own(_t, new_fst, snd0);
            //@ close Pair_full_borrow_content::<A, B>(_t, self)();
            //@ close_full_borrow(Pair_full_borrow_content::<A, B>(_t, self));
            //@ leak full_borrow(_, _);
            result
        }
    }

    pub fn replace_snd<'a>(&'a mut self, new_snd: B) -> B {
        unsafe {
            //@ open_full_borrow(_q_a, 'a, Pair_full_borrow_content::<A, B>(_t, self));
            //@ open Pair_full_borrow_content::<A, B>(_t, self)();
            //@ open Pair_own(_t, ?fst0, ?snd0);
            //@ open Pair_snd(self, snd0);
            let result = std::ptr::read(&self.snd);
            std::ptr::write(&mut self.snd, new_snd);
            //@ close Pair_snd(self, new_snd);
            //@ close Pair_own(_t, fst0, new_snd);
            //@ close Pair_full_borrow_content::<A, B>(_t, self)();
            //@ close_full_borrow(Pair_full_borrow_content::<A, B>(_t, self));
            //@ leak full_borrow(_, _);
            result
        }
    }
    
    pub fn deref_fst_mut<'a>(&'a mut self) -> &'a mut A {
        //@ Pair_split_full_borrow('a, _t, self);
        //@ leak full_borrow('a, <B>.full_borrow_content(_t, &(*self).snd));
        &mut self.fst
    }

    pub fn deref_snd_mut<'a>(&'a mut self) -> &'a mut B {
        //@ Pair_split_full_borrow('a, _t, self);
        //@ leak full_borrow('a, <A>.full_borrow_content(_t, &(*self).fst));
        &mut self.snd
    }
    
}
