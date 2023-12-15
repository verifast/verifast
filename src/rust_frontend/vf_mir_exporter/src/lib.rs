#![feature(rustc_private)]
#![feature(drain_filter)]
#![feature(box_patterns)]
#![feature(split_array)]

/***
 * Todo @Nima:
 * 1- Is it really necessary to register queries? read mir pretty printer.
 * The mir pretty printer uses optimized_mir/promoted_mir which are lower level generated mir
 * 2- Possible alternative way to get mir: tcx.mir_keys() and then convert the LocalDefId to DefId and
 * just call tcx.optimized_mir(def_id). These all should happen in the same place compiler may call
 * mir::pretty::write_mir_pretty(...)
 */

/***
 * This program is written based on "rust/src/test/run-make-fulldeps/obtain-borrowck"
 * This program implements a rustc driver that retrieves MIR bodies with
 * borrowck information. This cannot be done in a straightforward way because
 * `get_body_with_borrowck_facts`–the function for retrieving a MIR body with
 * borrowck facts–can panic if the body is stolen before it is invoked.
 * Therefore, the driver overrides `mir_borrowck` query (this is done in the
 * `config` callback), which retrieves the body that is about to be borrow
 * checked and stores it in a thread local `MIR_BODIES`. Then, `after_analysis`
 * callback triggers borrow checking of all MIR bodies by retrieving
 * `optimized_mir` and pulls out the MIR bodies with the borrowck information
 * from the thread local storage.
 */

extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

mod hir_utils;
mod preprocessor;

use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_driver::Compilation;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::itemlikevisit::ItemLikeVisitor;
use rustc_interface::interface::Compiler;
use rustc_interface::{Config, Queries};
use rustc_middle::mir;
use rustc_middle::ty::query::query_values::mir_borrowck;
use rustc_middle::ty::query::{ExternProviders, Providers};
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::Session;
use std::cell::RefCell;
use std::collections::HashMap;
use std::thread_local;
use tracing::{debug, error, info, trace, Level};

pub fn run_compiler() -> i32 {
    rustc_driver::catch_with_exit_code(move || {
        let mut rustc_args: Vec<_> = std::env::args().collect();
        rustc_args.push("-Coverflow_checks=off".to_owned());
        // To also compile crates without a main function
        // Todo @Nima: Should it not be passed from VeriFast?
        rustc_args.push("--crate-type=lib".to_owned());
        // We must pass -Zpolonius so that the borrowck information is computed.
        rustc_args.push("-Zpolonius".to_owned());
        // To have MIR dump annotated with lifetimes
        rustc_args.push("-Zverbose".to_owned());

        // Todo @Nima: Find the correct sysroot by yourself. for now we get it as an argument.
        // See filesearch::get_or_default_sysroot()

        let mut callbacks = CompilerCalls {
            ghost_ranges: Vec::new(),
        };
        // Call the Rust compiler with our callbacks.
        trace!("Calling the Rust Compiler with args: {:?}", rustc_args);
        rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks).run()
    })
}

#[derive(Default)]
struct CompilerCalls {
    ghost_ranges: Vec<preprocessor::GhostRange>,
}

impl rustc_driver::Callbacks for CompilerCalls {
    // In this callback we override the mir_borrowck query.
    fn config(&mut self, config: &mut Config) {
        let path = match &config.input {
            rustc_session::config::Input::File(path) => path.clone(),
            _ => {
                panic!("File expected");
            }
        };
        let contents = std::fs::read_to_string(&path).unwrap();
        let preprocessed_contents =
            preprocessor::preprocess(contents.as_str(), &mut self.ghost_ranges);
        config.input = rustc_session::config::Input::Str {
            name: rustc_span::FileName::Real(rustc_span::RealFileName::LocalPath(path)),
            input: preprocessed_contents,
        };
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }

    // In this callback we trigger borrow checking of all functions and obtain
    // the result.
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        queries.global_ctxt().unwrap().peek_mut().enter(|tcx| {
            /*** Collecting Annotations */
            // TODO: Get comments from preprocessor

            /*** Collecting MIR bodies */
            trace!("Collecting MIR bodies");
            // Collect definition ids of bodies.
            let hir = tcx.hir();
            let mut visitor = HirVisitor { bodies: Vec::new() };
            hir.visit_all_item_likes(&mut visitor);

            // Trigger borrow checking of all bodies.
            for def_id in visitor.bodies {
                let _ = tcx.optimized_mir(def_id);
            }

            // See what bodies were borrow checked.
            let bodies_and_facts = get_bodies(tcx);

            let bodies: Vec<_> = bodies_and_facts
                .iter()
                .map(|(def_path, body)| {
                    assert!(body.input_facts.cfg_edge.len() > 0);
                    debug!("We have body for {}", def_path);
                    &body.body
                })
                .collect();

            let mut vf_mir_capnp_builder = vf_mir_builder::VfMirCapnpBuilder::new(tcx);
            trace!("Ghost Ranges:\n{:#?}", self.ghost_ranges);
            for gr in &self.ghost_ranges {
                debug!("{:?}", gr.span());
            }
            vf_mir_capnp_builder.add_comments(&mut self.ghost_ranges);
            vf_mir_capnp_builder.add_bodies(bodies.as_slice());
            let msg_cpn = vf_mir_capnp_builder.build();
            capnp::serialize::write_message(&mut ::std::io::stdout(), msg_cpn.borrow_inner());
        });
        Compilation::Stop
    }
}

fn override_queries(_session: &Session, local: &mut Providers, _external: &mut ExternProviders) {
    local.mir_borrowck = mir_borrowck;
}

// Since mir_borrowck does not have access to any other state, we need to use a
// thread-local for storing the obtained MIR bodies.
//
// Note: We are using 'static lifetime here, which is in general unsound.
// Unfortunately, that is the only lifetime allowed here. Our use is safe
// because we cast it back to `'tcx` before using.
thread_local! {
    pub static MIR_BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> mir_borrowck<'tcx> {
    let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
        tcx,
        ty::WithOptConstParam::unknown(def_id),
    );
    // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
    let body_with_facts: BodyWithBorrowckFacts<'static> =
        unsafe { std::mem::transmute(body_with_facts) };
    MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        assert!(map.insert(def_id, body_with_facts).is_none());
    });
    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

/// Visitor that collects all body definition ids mentioned in the program.
struct HirVisitor {
    bodies: Vec<LocalDefId>,
}

impl<'tcx> ItemLikeVisitor<'tcx> for HirVisitor {
    fn visit_item(&mut self, item: &rustc_hir::Item) {
        match item.kind {
            rustc_hir::ItemKind::Fn(..) => self.bodies.push(item.def_id),
            // We cannot send DefId of a struct to optimize_mir query
            rustc_hir::ItemKind::Struct(..) => (),
            _ => (),
        }
    }

    fn visit_trait_item(&mut self, trait_item: &rustc_hir::TraitItem) {
        if let rustc_hir::TraitItemKind::Fn(_, trait_fn) = &trait_item.kind {
            if let rustc_hir::TraitFn::Provided(_) = trait_fn {
                self.bodies.push(trait_item.def_id);
            }
        }
    }

    fn visit_impl_item(&mut self, impl_item: &rustc_hir::ImplItem) {
        if let rustc_hir::ImplItemKind::Fn(..) = impl_item.kind {
            self.bodies.push(impl_item.def_id);
        }
    }

    fn visit_foreign_item(&mut self, _foreign_item: &rustc_hir::ForeignItem) {}
}

/// Pull MIR bodies stored in the thread-local.
fn get_bodies<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<(String, BodyWithBorrowckFacts<'tcx>)> {
    MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        map.drain()
            .map(|(def_id, body)| {
                let def_path = tcx.def_path(def_id.to_def_id());
                // SAFETY: For soundness we need to ensure that the bodies have
                // the same lifetime (`'tcx`), which they had before they were
                // stored in the thread local.
                (def_path.to_string_no_crate_verbose(), body)
            })
            .collect()
    })
}

mod vf_mir_builder {
    mod capnp_utils;
    use crate::preprocessor::GhostRange;
    use crate::vf_mir_capnp::annotation as annot_cpn;
    use crate::vf_mir_capnp::body as body_cpn;
    use crate::vf_mir_capnp::hir as hir_cpn;
    use crate::vf_mir_capnp::ident as ident_cpn;
    use crate::vf_mir_capnp::mutability as mutability_cpn;
    use crate::vf_mir_capnp::span_data as span_data_cpn;
    use crate::vf_mir_capnp::symbol as symbol_cpn;
    use crate::vf_mir_capnp::ty as ty_cpn;
    use crate::vf_mir_capnp::unsafety as unsafety_cpn;
    use crate::vf_mir_capnp::vf_mir as vf_mir_cpn;
    use crate::vf_mir_capnp::visibility as visibility_cpn;
    use adt_def_cpn::variant_def as variant_def_cpn;
    use basic_block_cpn::operand as operand_cpn;
    use basic_block_cpn::rvalue as rvalue_cpn;
    use basic_block_cpn::statement as statement_cpn;
    use basic_block_cpn::terminator as terminator_cpn;
    use binary_op_data_cpn::bin_op as bin_op_cpn;
    use unary_op_data_cpn::un_op as un_op_cpn;
    use body_cpn::basic_block as basic_block_cpn;
    use body_cpn::basic_block_id as basic_block_id_cpn;
    use body_cpn::const_value as const_value_cpn;
    use body_cpn::constant as constant_cpn;
    use body_cpn::contract as contract_cpn;
    use body_cpn::local_decl as local_decl_cpn;
    use body_cpn::local_decl_id as local_decl_id_cpn;
    use body_cpn::place as place_cpn;
    use body_cpn::scalar as scalar_cpn;
    use body_cpn::source_info as source_info_cpn;
    use body_cpn::var_debug_info as var_debug_info_cpn;
    use constant_cpn::constant_kind as constant_kind_cpn;
    use file_name_cpn::real_file_name as real_file_name_cpn;
    use hir_cpn::generics as hir_generics_cpn;
    use hir_generic_param_cpn::generic_param_kind as hir_generic_param_kind_cpn;
    use hir_generic_param_cpn::param_name as hir_generic_param_name_cpn;
    use hir_generics_cpn::generic_param as hir_generic_param_cpn;
    use loc_cpn::char_pos as char_pos_cpn;
    use loc_cpn::source_file as source_file_cpn;
    use mir::HasLocalDecls;
    use place_cpn::place_element as place_element_cpn;
    use ref_data_cpn::borrow_kind as borrow_kind_cpn;
    use rustc_ast::util::comments::Comment;
    use rustc_hir as hir;
    use rustc_middle::bug;
    use rustc_middle::ty;
    use rustc_middle::{mir, ty::TyCtxt};
    use rvalue_cpn::aggregate_data::aggregate_kind as aggregate_kind_cpn;
    use rvalue_cpn::binary_op_data as binary_op_data_cpn;
    use rvalue_cpn::unary_op_data as unary_op_data_cpn;
    use rvalue_cpn::cast_data::cast_kind as cast_kind_cpn;
    use rvalue_cpn::ref_data as ref_data_cpn;
    use source_file_cpn::file_name as file_name_cpn;
    use span_data_cpn::loc as loc_cpn;
    use statement_cpn::statement_kind as statement_kind_cpn;
    use std::collections::LinkedList;
    use switch_int_data_cpn::switch_targets as switch_targets_cpn;
    use terminator_cpn::terminator_kind as terminator_kind_cpn;
    use terminator_kind_cpn::fn_call_data as fn_call_data_cpn;
    use terminator_kind_cpn::switch_int_data as switch_int_data_cpn;
    use tracing::{debug, trace};
    use ty_cpn::adt_def as adt_def_cpn;
    use ty_cpn::adt_def_id as adt_def_id_cpn;
    use ty_cpn::adt_kind as adt_kind_cpn;
    use ty_cpn::adt_ty as adt_ty_cpn;
    use ty_cpn::const_ as ty_const_cpn;
    use ty_cpn::const_kind as const_kind_cpn;
    use ty_cpn::fn_def_ty as fn_def_ty_cpn;
    use ty_cpn::gen_arg as gen_arg_cpn;
    use ty_cpn::int_ty as int_ty_cpn;
    use ty_cpn::raw_ptr_ty as raw_ptr_ty_cpn;
    use ty_cpn::ref_ty as ref_ty_cpn;
    use ty_cpn::region as region_cpn;
    use ty_cpn::ty_kind as ty_kind_cpn;
    use ty_cpn::u_int_ty as u_int_ty_cpn;
    use var_debug_info_cpn::var_debug_info_contents as var_debug_info_contents_cpn;
    use variant_def_cpn::field_def as field_def_cpn;

    enum EncKind<'tcx, 'a> {
        Body(&'a mir::Body<'tcx>),
        Adt,
    }
    struct EncCtx<'tcx, 'a> {
        req_adts: Vec<&'tcx ty::AdtDef>,
        tcx: TyCtxt<'tcx>,
        mode: EncKind<'tcx, 'a>,
        annots: LinkedList<GhostRange>,
    }

    impl<'tcx, 'a> EncCtx<'tcx, 'a> {
        pub fn new(
            tcx: TyCtxt<'tcx>,
            mode: EncKind<'tcx, 'a>,
            annots: LinkedList<GhostRange>,
        ) -> Self {
            Self {
                req_adts: Vec::new(),
                tcx,
                mode,
                annots,
            }
        }
        pub fn add_req_adt(&mut self, adt: &'tcx ty::AdtDef) {
            /* Todo @Nima: It is necessary to encode the dependency between the required definitions.
                Because the order of definitions will matter in most of the analyzers.
            */
            self.req_adts.push(adt);
        }
        pub fn get_req_adts(&self) -> &Vec<&'tcx ty::AdtDef> {
            &self.req_adts
        }
        pub fn body(&self) -> &'a mir::Body<'tcx> {
            match self.mode {
                EncKind::Body(body) => body,
                _ => bug!(),
            }
        }
    }

    pub struct VfMirCapnpBuilder<'tcx, 'a> {
        tcx: TyCtxt<'tcx>,
        bodies: Vec<&'a mir::Body<'tcx>>,
        annots: LinkedList<GhostRange>,
    }

    impl<'tcx: 'a, 'a> VfMirCapnpBuilder<'tcx, 'a> {
        pub fn new(tcx: TyCtxt<'tcx>) -> VfMirCapnpBuilder {
            VfMirCapnpBuilder {
                tcx,
                bodies: Vec::new(),
                annots: LinkedList::new(),
            }
        }

        pub fn add_comments(&mut self, annots: &mut Vec<GhostRange>) {
            self.annots.extend(
                annots
                    .drain_filter(|annot| !annot.is_dummy())
                    .collect::<LinkedList<_>>(),
            );
        }

        pub fn add_bodies(&mut self, bodies: &[&'a mir::Body<'tcx>]) {
            self.bodies.extend_from_slice(bodies)
        }

        pub fn build(mut self) -> ::capnp::message::TypedBuilder<vf_mir_cpn::Owned> {
            let mut msg_cpn = ::capnp::message::TypedBuilder::<vf_mir_cpn::Owned>::new_default();
            let vf_mir_cpn = msg_cpn.init_root();
            self.encode_mir(vf_mir_cpn);
            msg_cpn
        }

        fn encode_mir(&mut self, mut vf_mir_cpn: vf_mir_cpn::Builder<'_>) {
            let bodies = &self.bodies;
            let len = bodies.len();
            let len = len.try_into().expect(&format!(
                "{} MIR bodies cannot be stored in a Capnp message",
                len
            ));
            let mut bodies_cpn = vf_mir_cpn.reborrow().init_bodies(len);

            let mut req_adt_defs = Vec::new();
            for (idx, body) in bodies.iter().enumerate() {
                let body_span = body.span.data();
                let annots = self
                    .annots
                    .drain_filter(|annot| {
                        body_span.contains(
                            annot
                                .span()
                                .expect("Dummy annot found during serialization")
                                .data(),
                        )
                    })
                    .collect::<LinkedList<_>>();
                let mut enc_ctx = EncCtx::new(self.tcx, EncKind::Body(body), annots);
                let body_cpn = bodies_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_body(&mut enc_ctx, body_cpn);
                req_adt_defs.extend(enc_ctx.get_req_adts());
            }

            // Encode Ghost Declarations
            let ghost_decl_batches = self
                .annots
                .drain_filter(|annot| {
                    let annot_span = annot
                        .span()
                        .expect("Dummy annotation found during serialization");
                    if let Some(body) = bodies.iter().find(|body| body.span.overlaps(annot_span)) {
                        panic!(
                            "Overlapping Ghost Declaration Block at {:?} and Function at {:?}",
                            annot_span, body.span
                        )
                    }
                    true
                })
                .collect::<LinkedList<_>>();
            let len = ghost_decl_batches.len();
            let len = len.try_into().expect(&format!(
                "{} ghost declaration blocks cannot be stored in a Capnp message",
                len
            ));
            let mut gh_decl_bs_cpn = vf_mir_cpn.reborrow().init_ghost_decl_batches(len);
            for (idx, gh_decl_b) in ghost_decl_batches.into_iter().enumerate() {
                let gh_decl_b_cpn = gh_decl_bs_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_annotation(self.tcx, gh_decl_b, gh_decl_b_cpn);
            }

            // Encode Required Definitions
            let mut adt_defs_cpn = vf_mir_cpn.init_adt_defs();
            let mut encoded_adt_defs = Vec::new();
            while !req_adt_defs.is_empty() {
                let it = req_adt_defs.into_iter();
                req_adt_defs = Vec::new();
                for adt_def in it {
                    match encoded_adt_defs
                        .iter()
                        .find(|&&enc_adt_def| enc_adt_def == adt_def)
                    {
                        Option::None => {
                            let mut adt_defs_cons_cpn = adt_defs_cpn.init_cons();
                            let adt_def_cpn = adt_defs_cons_cpn.reborrow().init_h();
                            let mut enc_ctx =
                                EncCtx::new(self.tcx, EncKind::Adt, LinkedList::new());
                            Self::encode_adt_def(self.tcx, &mut enc_ctx, adt_def, adt_def_cpn);
                            req_adt_defs.extend(enc_ctx.get_req_adts());
                            encoded_adt_defs.push(adt_def);
                            adt_defs_cpn = adt_defs_cons_cpn.init_t();
                        }
                        Option::Some(_) => (), //skip
                    }
                }
            }
            adt_defs_cpn.set_nil(());
        }

        fn encode_adt_def_id(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            adt_did: hir::def_id::DefId,
            mut adt_did_cpn: adt_def_id_cpn::Builder<'_>,
        ) {
            adt_did_cpn.set_name(&enc_ctx.tcx.def_path_str(adt_did));
        }

        fn encode_adt_def(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            adt_def: &ty::AdtDef,
            mut adt_def_cpn: adt_def_cpn::Builder<'_>,
        ) {
            debug!("Encoding ADT definition {:?}", adt_def);
            let id_cpn = adt_def_cpn.reborrow().init_id();
            Self::encode_adt_def_id(enc_ctx, adt_def.did, id_cpn);
            let len = adt_def.variants.len();
            let len = len.try_into().expect(&format!(
                "{} Variants cannot be stored in a Capnp message",
                len
            ));
            let mut variants_cpn = adt_def_cpn.reborrow().init_variants(len);
            for (idx, variant) in adt_def.variants.iter_enumerated() {
                let variant_cpn = variants_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_variant_def(tcx, enc_ctx, variant, variant_cpn);
            }
            let kind_cpn = adt_def_cpn.reborrow().init_kind();
            Self::encode_adt_kind(adt_def.adt_kind(), kind_cpn);
            let span_cpn = adt_def_cpn.reborrow().init_span();
            let span = tcx.def_span(adt_def.did);
            Self::encode_span_data(tcx, &span.data(), span_cpn);
            let vis_cpn = adt_def_cpn.reborrow().init_vis();
            let vis = tcx.visibility(adt_def.did);
            Self::encode_visibility(vis, vis_cpn);
            let is_local = adt_def.did.is_local();
            adt_def_cpn.set_is_local(is_local);
            debug!(
                "Adt def {:?} Visibility:{:?} Local:{}",
                adt_def, vis, is_local
            );
        }

        fn encode_adt_kind(adt_kind: ty::AdtKind, mut adt_kind_cpn: adt_kind_cpn::Builder<'_>) {
            match adt_kind {
                ty::AdtKind::Struct => adt_kind_cpn.set_struct_kind(()),
                ty::AdtKind::Union => adt_kind_cpn.set_enum_kind(()),
                ty::AdtKind::Enum => adt_kind_cpn.set_union_kind(()),
            }
        }

        fn encode_variant_def(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            vdef: &ty::VariantDef,
            vdef_cpn: variant_def_cpn::Builder<'_>,
        ) {
            let len = vdef.fields.len();
            let len = len.try_into().expect(&format!(
                "{} Fields cannot be stored in a Capnp message",
                len
            ));
            let mut fields_cpn = vdef_cpn.init_fields(len);
            for (idx, field) in vdef.fields.iter().enumerate() {
                let field_cpn = fields_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_field_def(tcx, enc_ctx, field, field_cpn);
            }
        }

        fn encode_field_def(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            fdef: &ty::FieldDef,
            mut fdef_cpn: field_def_cpn::Builder<'_>,
        ) {
            debug!("Encoding field definition {}", fdef.name);
            let name_cpn = fdef_cpn.reborrow().init_name();
            Self::encode_symbol(&fdef.name, name_cpn);
            let ty_cpn = fdef_cpn.reborrow().init_ty();
            let ty = tcx.type_of(fdef.did);
            Self::encode_ty(tcx, enc_ctx, &ty, ty_cpn);
            let vis_cpn = fdef_cpn.reborrow().init_vis();
            Self::encode_visibility(fdef.vis, vis_cpn);
            let span_cpn = fdef_cpn.init_span();
            let span = tcx.def_span(fdef.did);
            Self::encode_span_data(tcx, &span.data(), span_cpn);
        }

        fn encode_visibility(vis: ty::Visibility, mut vis_cpn: visibility_cpn::Builder<'_>) {
            match vis {
                ty::Visibility::Public => vis_cpn.set_public(()),
                ty::Visibility::Restricted(_did) => vis_cpn.set_restricted(()),
                ty::Visibility::Invisible => vis_cpn.set_invisible(()),
            }
        }

        fn encode_body(enc_ctx: &mut EncCtx<'tcx, 'a>, mut body_cpn: body_cpn::Builder<'_>) {
            let tcx = enc_ctx.tcx;
            let body = enc_ctx.body();
            trace!("Encoding MIR: {:?}", body.source.instance);
            debug!(
                "Encoding MIR for {:?} with span {:?}\n{}",
                body.source.instance,
                body.span,
                crate::mir_utils::mir_body_pretty_string(tcx, body)
            );

            let def_id = body.source.def_id();

            let kind = tcx.def_kind(def_id);
            match kind {
                hir::def::DefKind::Fn|hir::def::DefKind::AssocFn => {
                    let mut def_kind_cpn = body_cpn.reborrow().init_def_kind();
                    def_kind_cpn.set_fn(());
                }
                _ => std::todo!("Unsupported definition kind"),
            }

            let def_path = tcx.def_path_str(def_id);
            body_cpn.set_def_path(&def_path);

            Self::encode_unsafety(
                tcx.fn_sig(def_id).unsafety(),
                body_cpn.reborrow().init_unsafety(),
            );

            let hir_gens_cpn = body_cpn.reborrow().init_hir_generics();
            let hir_gens = tcx
                .hir()
                .get_generics(def_id.expect_local())
                .expect(&format!("Failed to get HIR generics data"));
            Self::encode_hir_generics(enc_ctx, hir_gens, hir_gens_cpn);

            let contract_cpn = body_cpn.reborrow().init_contract();
            let body_contract_span = crate::span_utils::body_contract_span(tcx, body);
            let contract_annots = enc_ctx
                .annots
                .drain_filter(|annot| {
                    body_contract_span.contains(annot.span().expect("Dummy span").data())
                })
                .collect::<LinkedList<_>>();
            Self::encode_contract(tcx, contract_annots, &body_contract_span, contract_cpn);

            let arg_count = body.arg_count.try_into().expect(&format!(
                "The number of args of {} cannot be stored in a Capnp message",
                def_path
            ));
            body_cpn.set_arg_count(arg_count);

            let local_decls_count = body.local_decls().len().try_into().expect(&format!(
                "The number of local declarations of {} cannot be stored in a Capnp message",
                def_path
            ));
            assert!(
                local_decls_count > arg_count,
                "Local declarations of {} are not more than its args",
                def_path
            );

            let mut local_decls_cpn = body_cpn.reborrow().init_local_decls(local_decls_count);
            for (idx, (local_decl_idx, local_decl)) in
                body.local_decls().iter_enumerated().enumerate()
            {
                let local_decl_cpn = local_decls_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_local_decl(tcx, enc_ctx, local_decl_idx, local_decl, local_decl_cpn);
            }

            let basic_blocks = body.basic_blocks();
            let basic_block_count = basic_blocks.len().try_into().expect(&format!(
                "The number of basic blocks of {} cannot be stored in a Capnp message",
                def_path
            ));
            let mut basic_blocks_cpn = body_cpn.reborrow().init_basic_blocks(basic_block_count);
            for (idx, (basic_block_idx, basic_block)) in basic_blocks.iter_enumerated().enumerate()
            {
                let basic_block_cpn = basic_blocks_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_basic_block(
                    tcx,
                    enc_ctx,
                    basic_block_idx,
                    basic_block,
                    basic_block_cpn,
                );
            }

            let span_cpn = body_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, &body.span.data(), span_cpn);

            let imp_span_cpn = body_cpn.reborrow().init_imp_span();
            let imp_span_data = crate::span_utils::body_imp_span(tcx, body);
            Self::encode_span_data(tcx, &imp_span_data, imp_span_cpn);

            let vdis_len = body.var_debug_info.len().try_into().expect(
                "The number of variables debug info entries cannot be stored in a Capnp message",
            );
            let mut vdis_cpn = body_cpn.reborrow().init_var_debug_info(vdis_len);
            for (idx, vdi) in body.var_debug_info.iter().enumerate() {
                let vdi_cpn = vdis_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_var_debug_info(tcx, enc_ctx, vdi, vdi_cpn);
            }

            let ghost_stmts = enc_ctx
                .annots
                .drain_filter(|annot| {
                    imp_span_data.contains(annot.span().expect("Dummy ghost range").data())
                })
                .collect::<LinkedList<_>>();
            assert!(
                enc_ctx.annots.is_empty(),
                "There are annotations for {} that are neither in contract nor in the body",
                def_path
            );
            let len = ghost_stmts.len();
            let len = len.try_into().expect(&format!(
                "{} ghost statements cannot be stored in a Capnp message",
                len
            ));
            let mut ghost_stmts_cpn = body_cpn.init_ghost_stmts(len);
            for (idx, ghost_stmt) in ghost_stmts.into_iter().enumerate() {
                let ghost_stmt_cpn = ghost_stmts_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_annotation(tcx, ghost_stmt, ghost_stmt_cpn);
            }
        }

        fn encode_unsafety(us: hir::Unsafety, mut us_cpn: unsafety_cpn::Builder<'_>) {
            match us {
                hir::Unsafety::Normal => us_cpn.set_safe(()),
                hir::Unsafety::Unsafe => us_cpn.set_unsafe(()),
            }
        }

        fn encode_hir_generics(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            hir_gens: &hir::Generics,
            mut hir_gens_cpn: hir_generics_cpn::Builder<'_>,
        ) {
            debug!("Encoding HIR generics {:?}", hir_gens);
            let len = hir_gens.params.len();
            let len = len.try_into().expect(&format!(
                "{} HIR generics cannot be stored in a Cpnp message",
                len
            ));
            let mut params_cpn = hir_gens_cpn.reborrow().init_params(len);
            for (idx, param) in hir_gens.params.iter().enumerate() {
                let param_cpn = params_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_hir_generic_param(enc_ctx, param, param_cpn);
            }
            let span_cpn = hir_gens_cpn.init_span();
            Self::encode_span_data(enc_ctx.tcx, &hir_gens.span.data(), span_cpn);
        }

        fn encode_hir_generic_param(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            p: &hir::GenericParam,
            mut p_cpn: hir_generic_param_cpn::Builder<'_>,
        ) {
            let name_cpn = p_cpn.reborrow().init_name();
            Self::encode_hir_generic_param_name(enc_ctx, &p.name, name_cpn);
            let span_cpn = p_cpn.reborrow().init_span();
            Self::encode_span_data(enc_ctx.tcx, &p.span.data(), span_cpn);
            p_cpn.set_pure_wrt_drop(p.pure_wrt_drop);
            let kind_cpn = p_cpn.init_kind();
            Self::encode_hir_generic_param_kind(&p.kind, kind_cpn);
        }

        fn encode_hir_generic_param_kind(
            gpk: &hir::GenericParamKind,
            mut gpk_cpn: hir_generic_param_kind_cpn::Builder<'_>,
        ) {
            match gpk {
                hir::GenericParamKind::Lifetime { .. } => gpk_cpn.set_lifetime(()),
                hir::GenericParamKind::Type { .. } => gpk_cpn.set_type(()),
                hir::GenericParamKind::Const { .. } => gpk_cpn.set_const(()),
            }
        }

        fn encode_hir_generic_param_name(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            n: &hir::ParamName,
            n_cpn: hir_generic_param_name_cpn::Builder<'_>,
        ) {
            match n {
                hir::ParamName::Plain(ident) => {
                    let ident_cpn = n_cpn.init_plain();
                    Self::encode_ident(enc_ctx, ident, ident_cpn);
                }
                hir::ParamName::Fresh(id) => {
                    let id_cpn = n_cpn.init_fresh();
                    capnp_utils::encode_u_int128((*id).try_into().unwrap(), id_cpn);
                }
                hir::ParamName::Error => bug!(),
            }
        }

        fn encode_var_debug_info(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            vdi: &mir::VarDebugInfo<'tcx>,
            mut vdi_cpn: var_debug_info_cpn::Builder<'_>,
        ) {
            debug!("Encoding VarDebugInfo {:?}", vdi);
            let name_cpn = vdi_cpn.reborrow().init_name();
            Self::encode_symbol(&vdi.name, name_cpn);
            let src_info_cpn = vdi_cpn.reborrow().init_source_info();
            Self::encode_source_info(tcx, &vdi.source_info, src_info_cpn);
            let value_cpn = vdi_cpn.init_value();
            Self::encode_var_debug_info_contents(tcx, enc_ctx, &vdi.value, value_cpn);
        }

        fn encode_var_debug_info_contents(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            vdi_contents: &mir::VarDebugInfoContents<'tcx>,
            vdi_contents_cpn: var_debug_info_contents_cpn::Builder<'_>,
        ) {
            match vdi_contents {
                mir::VarDebugInfoContents::Place(place) => {
                    let place_cpn = vdi_contents_cpn.init_place();
                    Self::encode_place(enc_ctx, place, place_cpn)
                }
                mir::VarDebugInfoContents::Const(constant) => {
                    let constant_cpn = vdi_contents_cpn.init_const();
                    Self::encode_constant(tcx, enc_ctx, constant, constant_cpn)
                }
            }
        }

        #[inline]
        fn encode_symbol(sym: &rustc_span::symbol::Symbol, mut sym_cpn: symbol_cpn::Builder<'_>) {
            sym_cpn.set_name(sym.as_str());
        }

        fn encode_ident(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ident: &rustc_span::symbol::Ident,
            mut ident_cpn: ident_cpn::Builder<'_>,
        ) {
            let name_cpn = ident_cpn.reborrow().init_name();
            Self::encode_symbol(&ident.name, name_cpn);
            let span_cpn = ident_cpn.init_span();
            Self::encode_span_data(enc_ctx.tcx, &ident.span.data(), span_cpn);
        }

        fn encode_span_data(
            tcx: TyCtxt<'tcx>,
            span_data: &rustc_span::SpanData,
            mut span_data_cpn: span_data_cpn::Builder<'_>,
        ) {
            debug!("Encoding SpanData {:?}", span_data);
            let sm = tcx.sess.source_map();
            let lo_cpn = span_data_cpn.reborrow().init_lo();
            let lo = sm.lookup_char_pos(span_data.lo);
            Self::encode_loc(&lo, lo_cpn);
            let hi_cpn = span_data_cpn.init_hi();
            let hi = sm.lookup_char_pos(span_data.hi);
            Self::encode_loc(&hi, hi_cpn);
        }

        fn encode_loc(loc: &rustc_span::Loc, mut loc_cpn: loc_cpn::Builder<'_>) {
            debug!("Encoding Loc {:?}", loc);
            let file_cpn = loc_cpn.reborrow().init_file();
            Self::encode_source_file(loc.file.as_ref(), file_cpn);

            let line = loc.line.try_into().expect(&format!(
                "The line number of source location cannot be stored in a Capnp message"
            ));
            loc_cpn.set_line(line);

            let col_cpn = loc_cpn.init_col();
            Self::encode_char_pos(&loc.col, col_cpn);
        }

        fn encode_char_pos(cpos: &rustc_span::CharPos, mut cpos_cpn: char_pos_cpn::Builder<'_>) {
            let pos = cpos.0.try_into().expect(&format!(
                "The column of source location cannot be storred in a Capnp message"
            ));
            cpos_cpn.set_pos(pos);
        }

        fn encode_source_file(
            src_file: &rustc_span::SourceFile,
            src_file_cpn: source_file_cpn::Builder<'_>,
        ) {
            debug!("Encoding SourceFile {:?}", src_file);
            let name_cpn = src_file_cpn.init_name();
            Self::encode_file_name(&src_file.name, name_cpn);
        }

        fn encode_file_name(fname: &rustc_span::FileName, fname_cpn: file_name_cpn::Builder<'_>) {
            debug!("Encoding FileName {:?}", fname);
            match fname {
                rustc_span::FileName::Real(real_fname) => {
                    let real_fname_cpn = fname_cpn.init_real();
                    Self::encode_real_file_name(real_fname, real_fname_cpn);
                }
                _ => todo!(),
            }
        }

        fn encode_real_file_name(
            real_fname: &rustc_span::RealFileName,
            mut real_fname_cpn: real_file_name_cpn::Builder<'_>,
        ) {
            debug!("Encoding RealFileName {:?}", real_fname);
            fn get_path_str(path_buf: &std::path::PathBuf) -> &str {
                path_buf.to_str().expect(&format!(
                    "Failed to get the unicode string of PathBuf {:?}",
                    path_buf
                ))
            }
            match real_fname {
                rustc_span::RealFileName::LocalPath(path_buf) => {
                    real_fname_cpn.set_local_path(get_path_str(path_buf));
                }
                rustc_span::RealFileName::Remapped {
                    local_path,
                    virtual_name,
                } => {
                    let mut remapped_data_cpn = real_fname_cpn.init_remapped();
                    let mut local_path_opt_cpn = remapped_data_cpn.reborrow().init_local_path();
                    match local_path {
                        None => local_path_opt_cpn.set_nothing(()),
                        Some(local_path) => {
                            let mut text_wrapper_cpn = local_path_opt_cpn.init_something();
                            text_wrapper_cpn.set_text(get_path_str(local_path));
                        }
                    }
                    remapped_data_cpn.set_virtual_name(get_path_str(virtual_name));
                }
            }
        }

        fn encode_contract(
            tcx: TyCtxt<'tcx>,
            contract_annots: LinkedList<GhostRange>,
            body_contract_span: &rustc_span::SpanData,
            mut contract_cpn: contract_cpn::Builder<'_>,
        ) {
            let span_cpn = contract_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, body_contract_span, span_cpn);
            let len = contract_annots.len().try_into().expect(&format!(
                "The number of contract annotations cannot be stored in a Capnp message"
            ));
            let mut annots_cpn = contract_cpn.init_annotations(len);
            for (idx, annot) in contract_annots.into_iter().enumerate() {
                let annot_cpn = annots_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_annotation(tcx, annot, annot_cpn);
            }
        }

        fn encode_annotation(
            tcx: TyCtxt<'tcx>,
            annot: GhostRange,
            mut annot_cpn: annot_cpn::Builder<'_>,
        ) {
            annot_cpn.set_raw(annot.contents());

            let span_cpn = annot_cpn.reborrow().init_span();
            Self::encode_span_data(
                tcx,
                &annot.span().expect("Dummy ghost range ").data(),
                span_cpn,
            );
            annot_cpn.set_start_line(annot.start_pos().line.try_into().unwrap());
            annot_cpn.set_start_col(annot.start_pos().column.try_into().unwrap());
            annot_cpn.set_end_line(annot.end_pos().line.try_into().unwrap());
            annot_cpn.set_end_col(annot.end_pos().column.try_into().unwrap());
        }

        fn encode_local_decl(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            local_decl_idx: mir::Local,
            local_decl: &mir::LocalDecl<'tcx>,
            mut local_decl_cpn: local_decl_cpn::Builder<'_>,
        ) {
            debug!("Encoding local decl {:?}", local_decl);
            let mutability_cpn = local_decl_cpn.reborrow().init_mutability();
            Self::encode_mutability(local_decl.mutability, mutability_cpn);

            let id_cpn = local_decl_cpn.reborrow().init_id();
            Self::encode_local_decl_id(local_decl_idx, id_cpn);

            let ty_cpn = local_decl_cpn.reborrow().init_ty();
            Self::encode_ty(tcx, enc_ctx, local_decl.ty, ty_cpn);

            let src_info_cpn = local_decl_cpn.init_source_info();
            Self::encode_source_info(tcx, &local_decl.source_info, src_info_cpn);
        }

        #[inline]
        fn encode_mutability(m: mir::Mutability, mut mutability_cpn: mutability_cpn::Builder<'_>) {
            match m {
                mir::Mutability::Mut => mutability_cpn.set_mut(()),
                mir::Mutability::Not => mutability_cpn.set_not(()),
            }
        }

        fn encode_local_decl_id(
            local_decl_idx: mir::Local,
            mut id_cpn: local_decl_id_cpn::Builder<'_>,
        ) {
            id_cpn.set_name(&format!("{:?}", local_decl_idx));
        }

        fn encode_ty(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ty: ty::Ty<'tcx>,
            ty_cpn: ty_cpn::Builder<'_>,
        ) {
            let mut ty_kind_cpn = ty_cpn.init_kind();
            match ty.kind() {
                ty::TyKind::Bool => ty_kind_cpn.set_bool(()),
                ty::TyKind::Int(int_ty) => {
                    let int_ty_cpn = ty_kind_cpn.init_int();
                    Self::encode_ty_int(int_ty, int_ty_cpn);
                }
                ty::TyKind::Uint(u_int_ty) => {
                    let u_int_ty_cpn = ty_kind_cpn.init_u_int();
                    Self::encode_ty_uint(u_int_ty, u_int_ty_cpn)
                }
                ty::TyKind::Char => ty_kind_cpn.set_char(()),
                ty::TyKind::Adt(adt_def, substs) => {
                    let adt_ty_cpn = ty_kind_cpn.init_adt();
                    Self::encode_ty_adt(tcx, enc_ctx, adt_def, substs, adt_ty_cpn);
                }
                ty::TyKind::RawPtr(ty_and_mut) => {
                    let raw_ptr_ty_cpn = ty_kind_cpn.init_raw_ptr();
                    Self::encode_ty_raw_ptr(tcx, enc_ctx, ty_and_mut, raw_ptr_ty_cpn);
                }
                ty::TyKind::Ref(region, ty, mutability) => {
                    let ref_ty_cpn = ty_kind_cpn.init_ref();
                    Self::encode_ty_ref(tcx, enc_ctx, region, ty, *mutability, ref_ty_cpn);
                }
                ty::TyKind::FnDef(def_id, substs) => {
                    let fn_def_ty_cpn = ty_kind_cpn.init_fn_def();
                    Self::encode_ty_fn_def(tcx, enc_ctx, def_id, substs, fn_def_ty_cpn);
                }
                ty::TyKind::FnPtr(_) => todo!("Function pointer type kind"),
                ty::TyKind::Never => ty_kind_cpn.set_never(()),
                ty::TyKind::Tuple(substs) => {
                    let len = substs.len().try_into().expect(&format!(
                        "The number of elements of the Tuple cannot be stored in a Capnp message"
                    ));
                    if len == 0
                    // Unit type
                    {
                        let tuple_ty_cpn = ty_kind_cpn.init_tuple(len);
                    } else {
                        todo!("Tuple types");
                    }
                }
                _ => todo!("Unsupported type kind"),
            }
        }

        fn encode_ty_int(int_ty: &ty::IntTy, mut int_ty_cpn: int_ty_cpn::Builder<'_>) {
            match int_ty {
                ty::IntTy::Isize => int_ty_cpn.set_i_size(()),
                ty::IntTy::I8 => int_ty_cpn.set_i8(()),
                ty::IntTy::I16 => int_ty_cpn.set_i16(()),
                ty::IntTy::I32 => int_ty_cpn.set_i32(()),
                ty::IntTy::I64 => int_ty_cpn.set_i64(()),
                ty::IntTy::I128 => int_ty_cpn.set_i128(()),
            }
        }

        fn encode_ty_uint(u_int_ty: &ty::UintTy, mut u_int_ty_cpn: u_int_ty_cpn::Builder<'_>) {
            match u_int_ty {
                ty::UintTy::Usize => u_int_ty_cpn.set_u_size(()),
                ty::UintTy::U8 => u_int_ty_cpn.set_u8(()),
                ty::UintTy::U16 => u_int_ty_cpn.set_u16(()),
                ty::UintTy::U32 => u_int_ty_cpn.set_u32(()),
                ty::UintTy::U64 => u_int_ty_cpn.set_u64(()),
                ty::UintTy::U128 => u_int_ty_cpn.set_u128(()),
            }
        }

        fn encode_ty_adt(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            adt_def: &'tcx ty::AdtDef,
            substs: ty::subst::SubstsRef<'tcx>,
            mut adt_ty_cpn: adt_ty_cpn::Builder<'_>,
        ) {
            debug!("Encoding algebraic data type {:?}", adt_def);
            let adt_did_cpn = adt_ty_cpn.reborrow().init_id();
            Self::encode_adt_def_id(enc_ctx, adt_def.did, adt_did_cpn);

            let len = substs.len().try_into().expect(&format!(
                "The number of generic args of {:?} cannot be stored in a Capnp message",
                adt_def
            ));
            let substs_cpn = adt_ty_cpn.reborrow().init_substs(len);
            Self::encode_ty_args(enc_ctx, substs, substs_cpn);

            let kind_cpn = adt_ty_cpn.init_kind();
            Self::encode_adt_kind(adt_def.adt_kind(), kind_cpn);
            // Definitions we use should be encoded later
            enc_ctx.add_req_adt(adt_def);
        }

        fn encode_ty_raw_ptr(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ty_and_mut: &ty::TypeAndMut<'tcx>,
            mut raw_ptr_ty_cpn: raw_ptr_ty_cpn::Builder<'_>,
        ) {
            let ty_cpn = raw_ptr_ty_cpn.reborrow().init_ty();
            Self::encode_ty(tcx, enc_ctx, ty_and_mut.ty, ty_cpn);
            let mut_cpn = raw_ptr_ty_cpn.init_mutability();
            Self::encode_mutability(ty_and_mut.mutbl, mut_cpn);
        }

        fn encode_ty_ref(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            region: ty::Region<'tcx>,
            ty: ty::Ty<'tcx>,
            mutability: mir::Mutability,
            mut ref_ty_cpn: ref_ty_cpn::Builder<'_>,
        ) {
            let region_cpn = ref_ty_cpn.reborrow().init_region();
            Self::encode_region(region, region_cpn);
            let ty_cpn = ref_ty_cpn.reborrow().init_ty();
            Self::encode_ty(tcx, enc_ctx, ty, ty_cpn);
            let mutability_cpn = ref_ty_cpn.init_mutability();
            Self::encode_mutability(mutability, mutability_cpn);
        }

        fn encode_ty_fn_def(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            def_id: &hir::def_id::DefId,
            substs: ty::subst::SubstsRef<'tcx>,
            mut fn_def_ty_cpn: fn_def_ty_cpn::Builder<'_>,
        ) {
            let def_path = tcx.def_path_str(*def_id);
            debug!("Encoding FnDef for {}", def_path);
            let mut id_cpn = fn_def_ty_cpn.reborrow().init_id();
            id_cpn.set_name(&def_path);
            let mut id_mono_cpn = fn_def_ty_cpn.reborrow().init_id_mono();
            if substs.is_empty() {
                id_mono_cpn.set_nothing(());
            } else {
                let def_path_mono = tcx.def_path_str_with_substs(*def_id, substs);
                debug!("Mono: {}", def_path_mono);
                let mut id_mono_cpn = id_mono_cpn.init_something();
                id_mono_cpn.set_name(&def_path_mono);
            }

            let len = substs.len().try_into().expect(&format!(
                "The number of generic args for {} cannot be stored in a Capnp message",
                def_path
            ));
            let substs_cpn = fn_def_ty_cpn.init_substs(len);
            Self::encode_ty_args(enc_ctx, substs, substs_cpn);
        }

        fn encode_region(region: ty::Region<'tcx>, mut region_cpn: region_cpn::Builder<'_>) {
            debug!("Encoding region {:?}", region);
            // MIR borrow-checker changes all regions to fresh `ReVar` and generates constraints for them and then tries to resolve the constraints
            // We do not expect to receive any other kind of `Region` because we are getting borrow-checked MIR
            match region {
                ty::RegionKind::ReEarlyBound(_early_bound_region) => bug!(),
                ty::RegionKind::ReLateBound(_debruijn_index, _bound_region) => bug!(),
                ty::RegionKind::ReFree(_free_region) => bug!(),
                ty::RegionKind::ReStatic => bug!(),
                ty::RegionKind::ReVar(_region_vid) => {
                    // Todo @Nima: We should find a mapping of `RegionVid`s and lifetime variable names at `hir`
                    region_cpn.set_id(/*&format!("{:?}", region)*/ "a");
                }
                ty::RegionKind::RePlaceholder(_placeholder_region) => bug!(),
                ty::RegionKind::ReEmpty(_universe_index) => bug!(),
                ty::RegionKind::ReErased => bug!(),
            }
        }

        fn encode_gen_arg(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            gen_arg: &ty::subst::GenericArg<'tcx>,
            gen_arg_cpn: gen_arg_cpn::Builder<'_>,
        ) {
            debug!("Encoding generic arg {:?}", gen_arg);
            let kind_cpn = gen_arg_cpn.init_kind();
            let kind = gen_arg.unpack();
            match kind {
                ty::subst::GenericArgKind::Lifetime(_) => todo!("Lifetime generic arg"),
                ty::subst::GenericArgKind::Type(ty) => {
                    let ty_cpn = kind_cpn.init_type();
                    Self::encode_ty(tcx, enc_ctx, ty, ty_cpn);
                }
                ty::subst::GenericArgKind::Const(_) => todo!("Const generic arg"),
            }
        }

        fn encode_basic_block(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            basic_block_idx: mir::BasicBlock,
            basic_block_data: &mir::BasicBlockData<'tcx>,
            mut basic_block_cpn: basic_block_cpn::Builder<'_>,
        ) {
            let basic_block_id_cpn = basic_block_cpn.reborrow().init_id();
            Self::encode_basic_block_id(basic_block_idx, basic_block_id_cpn);

            let statements_len = basic_block_data
                .statements
                .len()
                .try_into()
                .expect(&format!(
                    "The number of BasicBlock Statements cannot be stored in a Capnp message"
                ));
            let mut statements_cpn = basic_block_cpn.reborrow().init_statements(statements_len);
            for (idx, statement) in basic_block_data.statements.iter().enumerate() {
                let statement_cpn = statements_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_statement(tcx, enc_ctx, statement, statement_cpn);
            }

            let terminator_cpn = basic_block_cpn.reborrow().init_terminator();
            Self::encode_terminator(tcx, enc_ctx, basic_block_data.terminator(), terminator_cpn);

            basic_block_cpn.set_is_cleanup(basic_block_data.is_cleanup);
        }

        #[inline]
        fn encode_basic_block_id(
            basic_block_idx: mir::BasicBlock,
            mut basic_block_id_cpn: basic_block_id_cpn::Builder<'_>,
        ) {
            basic_block_id_cpn.set_name(&format!("{:?}", basic_block_idx));
        }

        fn encode_statement(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            statement: &mir::Statement<'tcx>,
            mut statement_cpn: statement_cpn::Builder<'_>,
        ) {
            let src_info_cpn = statement_cpn.reborrow().init_source_info();
            Self::encode_source_info(tcx, &statement.source_info, src_info_cpn);
            let kind_cpn = statement_cpn.init_kind();
            Self::encode_statement_kind(tcx, enc_ctx, &statement.kind, kind_cpn);
        }

        fn encode_source_info(
            tcx: TyCtxt<'tcx>,
            src_info: &mir::SourceInfo,
            mut src_info_cpn: source_info_cpn::Builder<'_>,
        ) {
            debug!("Encoding SourceInfo {:?}", src_info);
            let span_cpn = src_info_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, &src_info.span.data(), span_cpn);
            let scope_cpn = src_info_cpn.init_scope();
        }

        fn encode_statement_kind(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            statement_kind: &mir::StatementKind<'tcx>,
            mut statement_kind_cpn: statement_kind_cpn::Builder<'_>,
        ) {
            match statement_kind {
                mir::StatementKind::Assign(box (lhs_place, rhs_rval)) => {
                    let mut assign_data_cpn = statement_kind_cpn.init_assign();
                    let lhs_place_cpn = assign_data_cpn.reborrow().init_lhs_place();
                    Self::encode_place(enc_ctx, lhs_place, lhs_place_cpn);
                    let rhs_rvalue_cpn = assign_data_cpn.init_rhs_rvalue();
                    Self::encode_rvalue(tcx, enc_ctx, rhs_rval, rhs_rvalue_cpn);
                }
                mir::StatementKind::Nop => statement_kind_cpn.set_nop(()),
                // Todo @Nima: For now we do not support many statements and treat them as Nop
                _ => statement_kind_cpn.set_nop(()),
            }
        }

        fn encode_rvalue(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            rvalue: &mir::Rvalue<'tcx>,
            rvalue_cpn: rvalue_cpn::Builder<'_>,
        ) {
            debug!("Encoding Rvalue {:?}", rvalue);
            match rvalue {
                mir::Rvalue::Use(operand) => {
                    let operand_cpn = rvalue_cpn.init_use();
                    Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                }
                // [x; 32]
                mir::Rvalue::Repeat(operand, ty_const) => todo!(),
                // &x or &mut x
                mir::Rvalue::Ref(region, bor_kind, place) => {
                    let mut ref_data_cpn = rvalue_cpn.init_ref();
                    let region_cpn = ref_data_cpn.reborrow().init_region();
                    Self::encode_region(region, region_cpn);
                    let bor_kind_cpn = ref_data_cpn.reborrow().init_bor_kind();
                    Self::encode_borrow_kind(bor_kind, bor_kind_cpn);
                    let place_cpn = ref_data_cpn.init_place();
                    Self::encode_place(enc_ctx, place, place_cpn);
                }
                mir::Rvalue::ThreadLocalRef(def_id) => todo!(),
                mir::Rvalue::AddressOf(mutability, place) => {
                    let mut ao_data_cpn = rvalue_cpn.init_address_of();
                    let mutability_cpn = ao_data_cpn.reborrow().init_mutability();
                    Self::encode_mutability(*mutability, mutability_cpn);
                    let place_cpn = ao_data_cpn.init_place();
                    Self::encode_place(enc_ctx, place, place_cpn);
                }
                mir::Rvalue::Len(place) => todo!(),
                mir::Rvalue::Cast(cast_kind, operand, ty) => {
                    let mut cast_data_cpn = rvalue_cpn.init_cast();
                    let cast_kind_cpn = cast_data_cpn.reborrow().init_cast_kind();
                    Self::encode_cast_kind(cast_kind, cast_kind_cpn);
                    let operand_cpn = cast_data_cpn.reborrow().init_operand();
                    Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                    let ty_cpn = cast_data_cpn.init_ty();
                    Self::encode_ty(tcx, enc_ctx, ty, ty_cpn);
                }
                mir::Rvalue::BinaryOp(bin_op, box (operandl, operandr)) => {
                    let mut bin_op_data_cpn = rvalue_cpn.init_binary_op();
                    let bin_op_cpn = bin_op_data_cpn.reborrow().init_operator();
                    Self::encode_bin_op(*bin_op, bin_op_cpn);
                    let operandl_cpn = bin_op_data_cpn.reborrow().init_operandl();
                    Self::encode_operand(tcx, enc_ctx, operandl, operandl_cpn);
                    let operandr_cpn = bin_op_data_cpn.init_operandr();
                    Self::encode_operand(tcx, enc_ctx, operandr, operandr_cpn);
                }
                mir::Rvalue::CheckedBinaryOp(bin_op, box (operandl, operandr)) => todo!(),
                mir::Rvalue::NullaryOp(null_op, ty) => todo!(),
                mir::Rvalue::UnaryOp(un_op, operand) => {
                    let mut un_op_data_cpn = rvalue_cpn.init_unary_op();
                    let un_op_cpn = un_op_data_cpn.reborrow().init_operator();
                    Self::encode_un_op(*un_op, un_op_cpn);
                    let operand_cpn = un_op_data_cpn.reborrow().init_operand();
                    Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                }
                // Read the discriminant of an ADT.
                mir::Rvalue::Discriminant(place) => todo!(),
                // Creates an aggregate value, like a tuple or struct.
                mir::Rvalue::Aggregate(box aggregate_kind, operands) => {
                    let mut aggregate_data_cpn = rvalue_cpn.init_aggregate();
                    let aggregate_kind_cpn = aggregate_data_cpn.reborrow().init_aggregate_kind();
                    Self::encode_aggregate_kind(enc_ctx, aggregate_kind, aggregate_kind_cpn);
                    let len = operands.len();
                    let len = len.try_into().expect(&format!(
                        "{} operands cannot be stored in a Capnp message",
                        len
                    ));
                    let mut operands_cpn = aggregate_data_cpn.init_operands(len);
                    for (idx, operand) in operands.iter().enumerate() {
                        let operand_cpn = operands_cpn.reborrow().get(idx.try_into().unwrap());
                        Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                    }
                }
                // Transmutes a `*mut u8` into shallow-initialized `Box<T>`.
                mir::Rvalue::ShallowInitBox(operand, ty) => todo!(),
            }
        }

        fn encode_ty_args(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            targs: ty::subst::SubstsRef<'tcx>,
            mut targs_cpn: capnp::struct_list::Builder<'_, gen_arg_cpn::Owned>,
        ) {
            for (idx, targ) in targs.iter().enumerate() {
                let targ_cpn = targs_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_gen_arg(enc_ctx.tcx, enc_ctx, &targ, targ_cpn);
            }
        }

        fn encode_aggregate_kind(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            agg_kind: &mir::AggregateKind<'tcx>,
            agg_kind_cpn: aggregate_kind_cpn::Builder<'_>,
        ) {
            match agg_kind {
                mir::AggregateKind::Array(_ty) => todo!(),
                mir::AggregateKind::Tuple => todo!(),
                mir::AggregateKind::Adt(
                    def_id,
                    variant_idx,
                    substs,
                    _user_type_annot_idx_opt,
                    _union_active_field_opt,
                ) => {
                    if enc_ctx.tcx.adt_def(def_id.expect_local()).adt_kind() != ty::AdtKind::Struct
                    {
                        todo!()
                    }
                    let mut adt_data_cpn = agg_kind_cpn.init_adt();
                    let id_cpn = adt_data_cpn.reborrow().init_id();
                    Self::encode_adt_def_id(enc_ctx, *def_id, id_cpn);

                    let v_idx_cpn = adt_data_cpn.reborrow().init_variant_idx();
                    capnp_utils::encode_u_int128(
                        variant_idx.index().try_into().unwrap(),
                        v_idx_cpn,
                    );

                    let len = substs.len();
                    let len = len.try_into().expect(&format!(
                        "{} Generic args cannot be stored in a Capnp message",
                        len
                    ));
                    let substs_cpn = adt_data_cpn.reborrow().init_substs(len);
                    Self::encode_ty_args(enc_ctx, substs, substs_cpn);
                }
                mir::AggregateKind::Closure(_def_id, _substs) => todo!(),
                mir::AggregateKind::Generator(_def_id, _substs, _movability) => todo!(),
            }
        }

        fn encode_cast_kind(ck: &mir::CastKind, mut ck_cpn: cast_kind_cpn::Builder<'_>) {
            match ck {
                mir::CastKind::Misc => ck_cpn.set_misc(()),
                mir::CastKind::Pointer(_pointer_cast) => ck_cpn.set_pointer(()),
            }
        }

        fn encode_borrow_kind(bk: &mir::BorrowKind, mut bk_cpn: borrow_kind_cpn::Builder<'_>) {
            match bk {
                mir::BorrowKind::Shared => bk_cpn.set_shared(()),
                mir::BorrowKind::Shallow => bk_cpn.set_shallow(()),
                mir::BorrowKind::Unique => bk_cpn.set_unique(()),
                mir::BorrowKind::Mut {
                    allow_two_phase_borrow,
                } => {
                    let mut mut_data_cpn = bk_cpn.init_mut();
                    mut_data_cpn.set_allow_two_phase_borrow(*allow_two_phase_borrow);
                }
            }
        }

        fn encode_bin_op(bin_op: mir::BinOp, mut bin_op_cpn: bin_op_cpn::Builder<'_>) {
            match bin_op {
                mir::BinOp::Add => bin_op_cpn.set_add(()),
                mir::BinOp::Sub => bin_op_cpn.set_sub(()),
                mir::BinOp::Mul => bin_op_cpn.set_mul(()),
                mir::BinOp::Div => bin_op_cpn.set_div(()),
                mir::BinOp::Rem => bin_op_cpn.set_rem(()),
                mir::BinOp::BitXor => bin_op_cpn.set_bit_xor(()),
                mir::BinOp::BitAnd => bin_op_cpn.set_bit_and(()),
                mir::BinOp::BitOr => bin_op_cpn.set_bit_or(()),
                mir::BinOp::Shl => bin_op_cpn.set_shl(()),
                mir::BinOp::Shr => bin_op_cpn.set_shr(()),
                mir::BinOp::Eq => bin_op_cpn.set_eq(()),
                mir::BinOp::Lt => bin_op_cpn.set_lt(()),
                mir::BinOp::Le => bin_op_cpn.set_le(()),
                mir::BinOp::Ne => bin_op_cpn.set_ne(()),
                mir::BinOp::Ge => bin_op_cpn.set_ge(()),
                mir::BinOp::Gt => bin_op_cpn.set_gt(()),
                mir::BinOp::Offset => bin_op_cpn.set_offset(()),
            }
        }

        fn encode_un_op(un_op: mir::UnOp, mut un_op_cpn: un_op_cpn::Builder<'_>) {
            match un_op {
                mir::UnOp::Not => un_op_cpn.set_not(()),
                mir::UnOp::Neg => un_op_cpn.set_neg(()),
            }
        }

        fn encode_terminator(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            terminator: &mir::Terminator<'tcx>,
            mut terminator_cpn: terminator_cpn::Builder<'_>,
        ) {
            let src_info_cpn = terminator_cpn.reborrow().init_source_info();
            Self::encode_source_info(tcx, &terminator.source_info, src_info_cpn);
            let terminator_kind_cpn = terminator_cpn.init_kind();
            Self::encode_terminator_kind(tcx, enc_ctx, &terminator.kind, terminator_kind_cpn);
        }

        fn encode_terminator_kind(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            terminator_kind: &mir::TerminatorKind<'tcx>,
            mut terminator_kind_cpn: terminator_kind_cpn::Builder<'_>,
        ) {
            match terminator_kind {
                mir::TerminatorKind::Goto { target } => {
                    let target_cpn = terminator_kind_cpn.init_goto();
                    Self::encode_basic_block_id(*target, target_cpn);
                }
                mir::TerminatorKind::FalseUnwind {
                    real_target,
                    unwind,
                } => {
                    let target_cpn = terminator_kind_cpn.init_goto();
                    Self::encode_basic_block_id(*real_target, target_cpn);
                }
                mir::TerminatorKind::SwitchInt {
                    discr,
                    switch_ty,
                    targets,
                } => {
                    let switch_int_data_cpn = terminator_kind_cpn.init_switch_int();
                    Self::encode_switch_int_data(
                        tcx,
                        enc_ctx,
                        discr,
                        switch_ty,
                        targets,
                        switch_int_data_cpn,
                    );
                }
                mir::TerminatorKind::Resume => terminator_kind_cpn.set_resume(()),
                mir::TerminatorKind::Return => terminator_kind_cpn.set_return(()),
                mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    cleanup,
                    from_hir_call,
                    fn_span,
                } => {
                    let fn_call_data_cpn = terminator_kind_cpn.init_call();
                    Self::encode_fn_call_data(
                        tcx,
                        enc_ctx,
                        func,
                        args,
                        destination,
                        cleanup,
                        *from_hir_call,
                        fn_span,
                        fn_call_data_cpn,
                    );
                }
                _ => todo!("Unsupported Mir terminator kind"),
            }
        }

        fn encode_switch_int_data(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            discr: &mir::Operand<'tcx>,
            discr_ty: &ty::Ty<'tcx>,
            targets: &mir::terminator::SwitchTargets,
            mut switch_int_data_cpn: switch_int_data_cpn::Builder<'_>,
        ) {
            let discr_cpn = switch_int_data_cpn.reborrow().init_discr();
            Self::encode_operand(tcx, enc_ctx, discr, discr_cpn);
            let discr_ty_cpn = switch_int_data_cpn.reborrow().init_discr_ty();
            Self::encode_ty(tcx, enc_ctx, discr_ty, discr_ty_cpn);
            let targets_cpn = switch_int_data_cpn.init_targets();
            Self::encode_switch_targets(targets, targets_cpn);
        }

        fn encode_switch_targets(
            targets: &mir::terminator::SwitchTargets,
            mut targets_cpn: switch_targets_cpn::Builder<'_>,
        ) {
            debug!("Encoding Switch targets {:?}", targets);
            let len = targets
                .all_targets()
                .len()
                .checked_sub(1 /*`otherwise` case*/)
                .expect(&format!(
                    "Compiler invariant failed. SwitchInt must always have at least one branch"
                ));
            let len = len.try_into().expect(&format!(
                "{} Switch branches cannot be stored in a Capnp message",
                len
            ));
            let mut branches_cpn = targets_cpn.reborrow().init_branches(len);
            for (idx, (val, target)) in targets.iter().enumerate() {
                let mut branch_cpn = branches_cpn.reborrow().get(idx.try_into().unwrap());
                let val_cpn = branch_cpn.reborrow().init_val();
                capnp_utils::encode_u_int128(val, val_cpn);
                let target_cpn = branch_cpn.init_target();
                Self::encode_basic_block_id(target, target_cpn);
            }
            let otherwise_cpn = targets_cpn.init_otherwise();
            // Todo @Nima: For now there is always an `otherwise` case in SwitchInt targets. The compiler may change this invariant.
            let target_cpn = otherwise_cpn.init_something();
            Self::encode_basic_block_id(targets.otherwise(), target_cpn);
        }

        fn encode_fn_call_data(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            func: &mir::Operand<'tcx>,
            args: &Vec<mir::Operand<'tcx>>,
            destination: &Option<(mir::Place<'tcx>, mir::BasicBlock)>,
            cleanup: &Option<mir::BasicBlock>,
            from_hir_call: bool,
            fn_span: &rustc_span::Span,
            mut fn_call_data_cpn: fn_call_data_cpn::Builder<'_>,
        ) {
            let func_cpn = fn_call_data_cpn.reborrow().init_func();
            Self::encode_operand(tcx, enc_ctx, func, func_cpn);
            // Todo @Nima: Are these checks necessary
            let ty = match func {
                mir::Operand::Constant(box mir::Constant {
                    literal: mir::ConstantKind::Ty(ty::Const { ty, .. }),
                    ..
                }) => ty,
                _ => bug!("Function call terminator with callee operand {:?}", func),
            };

            let ty_kind = ty.kind();
            match ty_kind {
                ty::FnDef(..) | ty::FnPtr(_) => (),
                _ => bug!(
                    "Function call terminator with unexpected type kind {:?}",
                    ty_kind
                ),
            }

            // Encoding args
            let args_len = args.len().try_into().expect(&format!(
                "The number of arguments for function call cannot be stored in a Capnp message"
            ));
            let mut args_cpn = fn_call_data_cpn.reborrow().init_args(args_len);
            for (idx, arg) in args.iter().enumerate() {
                let arg_cpn = args_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_operand(tcx, enc_ctx, arg, arg_cpn);
            }

            // Encode destination
            let mut destination_cpn = fn_call_data_cpn.reborrow().init_destination();
            match destination {
                Option::None => destination_cpn.set_nothing(()), // diverging call
                Option::Some((dest_place, dest_bblock_id)) => {
                    let mut destination_data_cpn = destination_cpn.init_something();
                    let place_cpn = destination_data_cpn.reborrow().init_place();
                    Self::encode_place(enc_ctx, dest_place, place_cpn);
                    let basic_block_id_cpn = destination_data_cpn.init_basic_block_id();
                    Self::encode_basic_block_id(*dest_bblock_id, basic_block_id_cpn);
                }
            }

            fn_call_data_cpn.set_from_hir_call(from_hir_call);
            let fn_span_data_cpn = fn_call_data_cpn.init_fn_span();
            Self::encode_span_data(tcx, &fn_span.data(), fn_span_data_cpn);
        }

        fn encode_operand(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            operand: &mir::Operand<'tcx>,
            operand_cpn: operand_cpn::Builder<'_>,
        ) {
            debug!("Encoding Operand {:?}", operand);
            match operand {
                mir::Operand::Copy(place) => {
                    let place_cpn = operand_cpn.init_copy();
                    Self::encode_place(enc_ctx, place, place_cpn);
                }
                mir::Operand::Move(place) => {
                    let place_cpn = operand_cpn.init_move();
                    Self::encode_place(enc_ctx, place, place_cpn);
                }
                mir::Operand::Constant(box constant) => {
                    let constant_cpn = operand_cpn.init_constant();
                    Self::encode_constant(tcx, enc_ctx, constant, constant_cpn);
                }
            }
        }

        fn encode_constant(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            constant: &mir::Constant<'tcx>,
            mut constant_cpn: constant_cpn::Builder<'_>,
        ) {
            let span_data_cpn = constant_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, &constant.span.data(), span_data_cpn);
            let literal_cpn = constant_cpn.init_literal();
            Self::encode_constant_kind(tcx, enc_ctx, &constant.literal, literal_cpn);
        }

        fn encode_constant_kind(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            constant_kind: &mir::ConstantKind<'tcx>,
            constant_kind_cpn: constant_kind_cpn::Builder<'_>,
        ) {
            match constant_kind {
                mir::ConstantKind::Ty(ty_const) => {
                    let ty_const_cpn = constant_kind_cpn.init_ty();
                    Self::encode_typed_constant(tcx, enc_ctx, ty_const, ty_const_cpn);
                }
                mir::ConstantKind::Val(const_val, ty) => todo!(),
            }
        }

        fn encode_typed_constant(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ty_const: &ty::Const<'tcx>,
            mut ty_const_cpn: ty_const_cpn::Builder<'_>,
        ) {
            debug!("Encoding typed constant {:?}", ty_const);
            let ty_cpn = ty_const_cpn.reborrow().init_ty();
            Self::encode_ty(tcx, enc_ctx, ty_const.ty, ty_cpn);

            let val_cpn = ty_const_cpn.init_val();
            Self::encode_const_kind(tcx, ty_const.ty, &ty_const.val, val_cpn);
        }

        fn encode_const_kind(
            tcx: TyCtxt<'tcx>,
            ty: ty::Ty<'tcx>,
            const_kind: &ty::ConstKind<'tcx>,
            const_kind_cpn: const_kind_cpn::Builder<'_>,
        ) {
            use ty::ConstKind as CK;
            match const_kind {
                // A const generic parameter.
                CK::Param(param_const) => todo!(),
                // Infer the value of the const.
                CK::Infer(infer_const) => todo!(),
                // Bound const variable, used only when preparing a trait query.
                CK::Bound(debruijn_idx, bound_var) => todo!(),
                // A placeholder const - universally quantified higher-ranked const.
                CK::Placeholder(placeholder_const) => todo!(),
                // Used in the HIR by using `Unevaluated` everywhere and later normalizing to one of the other
                // variants when the code is monomorphic enough for that.
                CK::Unevaluated(unevaluated) => todo!(),
                // Used to hold computed value.
                CK::Value(const_value) => {
                    let const_value_cpn = const_kind_cpn.init_value();
                    Self::encode_const_value(tcx, ty, const_value, const_value_cpn);
                }
                // A placeholder for a const which could not be computed; this is
                // propagated to avoid useless error messages.
                CK::Error(delay_span_bug_emitted) => todo!(),
            }
        }

        fn encode_const_value(
            tcx: TyCtxt<'tcx>,
            ty: ty::Ty<'tcx>,
            const_value: &mir::interpret::ConstValue<'tcx>,
            const_value_cpn: const_value_cpn::Builder<'_>,
        ) {
            use mir::interpret::ConstValue as CV;
            match const_value {
                // Used only for types with `layout::abi::Scalar` ABI and ZSTs.
                CV::Scalar(scalar) => {
                    // `Scalar`s are a limited number of primitives.
                    // It is easier to encode the value itself instead of its internal representation in the compiler
                    let scalar_cpn = const_value_cpn.init_scalar();
                    Self::encode_scalar(tcx, ty, scalar, scalar_cpn);
                }
                // Used only for `&[u8]` and `&str`
                CV::Slice { data, start, end } => todo!(),
                // A value not represented/representable by `Scalar` or `Slice`
                CV::ByRef { alloc, offset } => todo!(),
            }
        }

        fn encode_scalar(
            tcx: TyCtxt<'tcx>,
            ty: ty::Ty<'tcx>,
            scalar: &mir::interpret::Scalar,
            mut scalar_cpn: scalar_cpn::Builder<'_>,
        ) {
            let gen_err_msg = "Failed to encode scalar";
            let err_msg = &format!(
                "{}. Cannot make a {:?} value out of the scalar {:?}",
                gen_err_msg, ty, scalar
            );
            match ty.kind() {
                ty::TyKind::Bool => {
                    let bv = scalar.to_bool().expect(err_msg);
                    scalar_cpn.set_bool(bv);
                }
                ty::TyKind::Char => {
                    let cv = scalar.to_char().expect(err_msg);
                    scalar_cpn.set_char(cv as u32);
                }
                ty::TyKind::Int(int_ty) => {
                    let mut int_val_cpn = scalar_cpn.init_int();
                    match int_ty {
                        ty::IntTy::Isize => {
                            let visz = scalar.to_machine_isize(&tcx).expect(err_msg);
                            capnp_utils::encode_int128(
                                visz.try_into().unwrap(),
                                int_val_cpn.init_isize(),
                            );
                        }
                        ty::IntTy::I8 => {
                            let vi8 = scalar.to_i8().expect(err_msg);
                            int_val_cpn.set_i8(vi8);
                        }
                        ty::IntTy::I16 => {
                            let vi16 = scalar.to_i16().expect(err_msg);
                            int_val_cpn.set_i16(vi16);
                        }
                        ty::IntTy::I32 => {
                            let vi32 = scalar.to_i32().expect(err_msg);
                            int_val_cpn.set_i32(vi32);
                        }
                        ty::IntTy::I64 => {
                            let vi64 = scalar.to_i64().expect(err_msg);
                            int_val_cpn.set_i64(vi64);
                        }
                        ty::IntTy::I128 => {
                            let vi128 = scalar.to_i128().expect(err_msg);
                            capnp_utils::encode_int128(vi128, int_val_cpn.init_i128());
                        }
                    }
                }
                ty::TyKind::Uint(uint_ty) => {
                    let mut uint_val_cpn = scalar_cpn.init_uint();
                    match uint_ty {
                        ty::UintTy::Usize => {
                            let vusz = scalar.to_machine_usize(&tcx).expect(err_msg);
                            capnp_utils::encode_u_int128(
                                vusz.try_into().unwrap(),
                                uint_val_cpn.init_usize(),
                            );
                        }
                        ty::UintTy::U8 => {
                            let vu8 = scalar.to_u8().expect(err_msg);
                            uint_val_cpn.set_u8(vu8);
                        }
                        ty::UintTy::U16 => {
                            let vu16 = scalar.to_u16().expect(err_msg);
                            uint_val_cpn.set_u16(vu16);
                        }
                        ty::UintTy::U32 => {
                            let vu32 = scalar.to_u32().expect(err_msg);
                            uint_val_cpn.set_u32(vu32);
                        }
                        ty::UintTy::U64 => {
                            let vu64 = scalar.to_u64().expect(err_msg);
                            uint_val_cpn.set_u64(vu64);
                        }
                        ty::UintTy::U128 => {
                            let vu128 = scalar.to_u128().expect(err_msg);
                            capnp_utils::encode_u_int128(vu128, uint_val_cpn.init_u128());
                        }
                    }
                }
                ty::TyKind::Float(float_ty) => todo!(),
                ty::TyKind::FnDef(def_id, substs) => scalar_cpn.set_fn_def(()),
                ty::TyKind::Tuple(substs) => {
                    for ty in ty.tuple_fields() {
                        todo!();
                    }
                }
                _ => panic!("{}. Type {:?} is not a scalar type.", gen_err_msg, ty),
            }
        }

        fn encode_place(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            place: &mir::Place<'tcx>,
            mut place_cpn: place_cpn::Builder<'_>,
        ) {
            use mir::tcx::PlaceTy;
            let local_decl_id_cpn = place_cpn.reborrow().init_local();
            Self::encode_local_decl_id(place.local, local_decl_id_cpn);

            let place_elms_len = place.projection.len().try_into().expect(&format!(
                "The number of projection elements cannot be stored in a Capnp message"
            ));
            let mut place_elms_cpn = place_cpn.init_projection(place_elms_len);
            let mut pty = PlaceTy::from_ty(enc_ctx.body().local_decls()[place.local].ty);
            for (idx, place_elm) in place.projection.iter().enumerate() {
                let place_elm_cpn = place_elms_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_place_element(enc_ctx, pty.ty, &place_elm, place_elm_cpn);
                pty = pty.projection_ty(enc_ctx.tcx, place_elm);
            }
        }

        fn encode_place_element(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ty: ty::Ty<'tcx>,
            place_elm: &mir::PlaceElem<'tcx>,
            mut place_elm_cpn: place_element_cpn::Builder<'_>,
        ) {
            debug!(
                "Encoding place element {:?} Projecting from {:?}",
                place_elm, ty
            );
            match place_elm {
                mir::ProjectionElem::Deref => place_elm_cpn.set_deref(()),
                mir::ProjectionElem::Field(field, fty) => {
                    let mut field_data_cpn = place_elm_cpn.init_field();
                    let idx_cpn = field_data_cpn.reborrow().init_idx();
                    capnp_utils::encode_u_int128(field.index().try_into().unwrap(), idx_cpn);
                    let adt_def = ty
                        .ty_adt_def()
                        .expect(&format!("{:?} type for a PlaceElem::Field projection", ty));
                    let name = adt_def.non_enum_variant().fields[field.index()].name;
                    let name_cpn = field_data_cpn.reborrow().init_name();
                    Self::encode_symbol(&name, name_cpn);
                    let ty_cpn = field_data_cpn.init_ty();
                    Self::encode_ty(enc_ctx.tcx, enc_ctx, fty, ty_cpn);
                    /* Todo @Nima: When `encode_ty` becomes a method of `EncCtx` there would not be
                     * such strange arguments `enc_ctx.tcx` and `enc_tcx`
                     */
                }
                _ => todo!(),
            }
        }
    }
}

// This module should be in the crate root because the generated code counts on it
mod vf_mir_capnp {
    #![allow(unused)]
    include!(concat!(env!("OUT_DIR"), "/vf_mir_capnp.rs"));
}

mod mir_utils {
    use rustc_hir::def_id::DefId;
    use rustc_middle::mir;
    use rustc_middle::ty::TyCtxt;

    pub fn mir_def_ids(tcx: TyCtxt<'_>) -> Vec<DefId> {
        tcx.mir_keys(())
            .iter()
            .map(|local_def_id| local_def_id.to_def_id())
            .collect()
    }

    pub fn mir_body_pretty_string<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> String {
        use rustc_middle::mir::pretty::write_mir_fn;
        let mut buf: Vec<u8> = Vec::new();
        write_mir_fn(tcx, body, &mut |_, _| Ok(()), &mut buf).expect(&format!(
            "Failed to generate pretty MIR for {:?}",
            body.source.instance
        ));
        let pretty_mir = String::from_utf8(buf).expect(&format!(
            "Failed to read pretty MIR string for {:?}",
            body.source.instance,
        ));
        pretty_mir
    }
}

mod span_utils {

    use crate::hir_utils;
    use rustc_ast::util::comments::Comment;
    use rustc_hir::def_id::DefId;
    use rustc_middle::{mir, ty::TyCtxt};
    use rustc_span::{BytePos, ExpnKind, Span, SpanData, SyntaxContext};
    use tracing::debug;

    // Copy from rustc_mir_transform/src/coverage/mod.rs
    fn get_hir_body_span<'tcx>(
        tcx: TyCtxt<'tcx>,
        hir_body: &rustc_hir::Body<'tcx>,
        def_id: DefId,
    ) -> Span {
        let mut body_span = hir_body.value.span;
        if tcx.is_closure(def_id) {
            // If the MIR function is a closure, and if the closure body span
            // starts from a macro, but it's content is not in that macro, try
            // to find a non-macro callsite, and instrument the spans there
            // instead.
            loop {
                let expn_data = body_span.ctxt().outer_expn_data();
                if expn_data.is_root() {
                    break;
                }
                if let ExpnKind::Macro { .. } = expn_data.kind {
                    body_span = expn_data.call_site;
                } else {
                    break;
                }
            }
        }
        body_span
    }

    pub fn body_imp_span<'tcx>(tcx: TyCtxt<'tcx>, mir_body: &mir::Body<'tcx>) -> SpanData {
        let def_id = mir_body.source.def_id();
        let hir_body = hir_utils::fn_body(tcx, def_id);
        let body_imp_span = get_hir_body_span(tcx, hir_body, def_id);
        debug!(
            "The body implementation span for {:?} at {:?} is {:?}",
            mir_body.source.instance, mir_body.span, body_imp_span
        );
        body_imp_span.data()
    }

    pub fn body_contract_span<'tcx>(tcx: TyCtxt<'tcx>, mir_body: &mir::Body<'tcx>) -> SpanData {
        let def_id = mir_body.source.def_id();
        let fn_sig = hir_utils::fn_sig(tcx, def_id);
        let hir_body = hir_utils::fn_body(tcx, def_id);
        let body_span = get_hir_body_span(tcx, hir_body, def_id);
        let cspan = fn_sig.span.shrink_to_hi().with_hi(body_span.lo());
        debug!(
            "Contract span for {:?} is {:?}",
            mir_body.source.instance, cspan
        );
        cspan.data()
    }

    /** BUG @Nima: In the case of BlockComment this calculation is wrong. We cannot calculate the span rightly.
     * The new line characters have been removed from the lines of the comment and we do not know if they are '\n' or "\r\n".
     * Moreover, the function that gathers comments removes the common whitespaces before all the lines of a BlockComment.
     * Thus, it is not possible to calculate the right span for a BlockComment using the rustc_ast::util::comments module.
     * Possible solutions are either writing a comment utility module ourselves or using macros to annotate Rust code in the way that Prusti does.
     * See rustc_ast::util::comments::split_block_comment_into_lines.
     */

    pub fn comment_span(cmt: &Comment) -> SpanData {
        let len: usize = cmt.lines.iter().map(|line| line.as_bytes().len()).sum();
        let hi = cmt.pos.0 as usize + len;
        let hi = BytePos(
            hi.try_into()
                .expect("The length of comment cannot fit in a BytePos type"),
        );
        SpanData {
            lo: cmt.pos,
            hi,
            //Todo @Nima: Check if the values we assign to below fields are sound
            ctxt: SyntaxContext::root(),
            parent: None,
        }
    }
}

mod vf_annot_utils {
    use rustc_ast::util::comments::Comment;

    pub fn is_vf_annot(cmt: &Comment) -> bool {
        if let Some(first_line) = cmt.lines.first() {
            if first_line.starts_with("//@") {
                return true;
            } else if first_line.starts_with("/*@") {
                let last_line = cmt.lines.last().unwrap();
                if last_line.ends_with("@*/") {
                    return true;
                }
            }
        }
        false
    }
}
// Todo @Nima: Some mut vars might not need to be mut.
// Todo @Nima: The encoding functions need to be turned to method to prevent passing context around
// Todo @Nima: Change the encode functions that require the EncCtx as a parameter to methods of EncCtx
// Todo @Nima: Extract lifetime beginning and ends to produce and consume their tokens in those compiler-inferred places
