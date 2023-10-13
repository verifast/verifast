use rustc_hir::def_id::DefId;
use rustc_middle::{hir, ty::TyCtxt};

pub fn fn_sig(tcx: TyCtxt<'_>, def_id: DefId) -> &rustc_hir::FnSig<'_> {
    tcx.hir()
        .get_if_local(def_id)
        .expect("expected DefId to be local")
        .fn_sig()
        .expect("expected DefId to be a function")
}

pub fn fn_body(tcx: TyCtxt<'_>, def_id: DefId) -> &rustc_hir::Body<'_> {
    let hir_node = tcx
        .hir()
        .get_if_local(def_id)
        .expect("expected DefId to be local");
    let fn_body_id =
        hir::map::associated_body(hir_node).expect("expected DefId to be a function with body");
    tcx.hir().body(fn_body_id)
}
