use rustc_hir::def_id::DefId;
use rustc_middle::{hir, ty::TyCtxt};

pub fn fn_sig(tcx: TyCtxt<'_>, def_id: DefId) -> &rustc_hir::FnSig<'_> {
    tcx.hir_node_by_def_id(def_id.expect_local())
       .fn_sig()
       .expect("expected DefId to be a function")
}

pub fn fn_body(tcx: TyCtxt<'_>, def_id: DefId) -> &rustc_hir::Body<'_> {
    tcx.hir_body_owned_by(def_id.expect_local())
}
