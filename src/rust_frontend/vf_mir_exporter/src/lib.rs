#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(split_array)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![deny(warnings)]

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

extern crate rustc_abi;
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
use rustc_interface::interface::Compiler;
use rustc_interface::Config;
use rustc_middle::mir;
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::Session;
use rustc_span::Span;
use std::cell::RefCell;
use std::collections::HashMap;
use std::thread_local;
use tracing::{debug, error, info, trace, Level};

#[derive(PartialEq)]
enum PreprocessMode {
    DoNotPreprocess,
    PreprocessReadOnly,
    Preprocess
}

pub fn run_compiler() -> i32 {
    rustc_driver::catch_with_exit_code(move || {
        let mut rustc_args: Vec<_> = std::env::args().collect();
        rustc_args.push("-Coverflow_checks=off".to_owned());
        // We must pass -Zpolonius so that the borrowck information is computed.
        //rustc_args.push("-Zpolonius".to_owned());
        // To have MIR dump annotated with lifetimes
        //rustc_args.push("-Zverbose_internals".to_owned());
        let mut preprocess_mode = PreprocessMode::Preprocess;
        if let Some(index) = rustc_args.iter().position(|arg| arg == "--vf-rust-mir-exporter:preprocess-readonly") {
            preprocess_mode = PreprocessMode::PreprocessReadOnly;
            rustc_args.remove(index);
        }
        if let Some(index) = rustc_args.iter().position(|arg| arg == "--vf-rust-mir-exporter:no-preprocess") {
            preprocess_mode = PreprocessMode::DoNotPreprocess;
            rustc_args.remove(index);
        }
        {
            // Find the index of the '--vf-rust-mir-exporter:no-default-args' argument.
            if let Some(index) = rustc_args
                .iter()
                .position(|arg| arg == "--vf-rust-mir-exporter:no-default-args") {
                // Remove the argument.
                rustc_args.remove(index);
            } else {
                // To also compile crates without a main function
                // Todo @Nima: Should it not be passed from VeriFast?
                rustc_args.push("--crate-type=lib".to_owned());
                rustc_args.push("--error-format=json".to_owned());
            }
        }

        // Todo @Nima: Find the correct sysroot by yourself. for now we get it as an argument.
        // See filesearch::get_or_default_sysroot()

        let mut callbacks = CompilerCalls {
            source_files: Box::leak(Box::new(std::sync::Mutex::new(SourceFiles::new()))),
            preprocess_mode,
        };
        // Call the Rust compiler with our callbacks.
        trace!("Calling the Rust Compiler with args: {:?}", rustc_args);
        rustc_driver::run_compiler(&rustc_args, &mut callbacks)
    })
}

struct SourceFile {
    path: Box<std::path::Path>,
    directives: Vec<Box<preprocessor::GhostRange>>,
    ghost_ranges: Vec<Box<preprocessor::GhostRange>>,
}

struct SourceFiles {
    source_files: Vec<SourceFile>,
}

impl SourceFiles {
    fn new() -> SourceFiles {
        SourceFiles {
            source_files: Vec::new(),
        }
    }

    fn push(&mut self, source_file: SourceFile) {
        self.source_files.push(source_file);
    }

    fn export_data(
        &mut self,
        all_directives: &mut Vec<Box<preprocessor::GhostRange>>,
        all_ghost_ranges: &mut Vec<Box<preprocessor::GhostRange>>,
        sm: &rustc_span::source_map::SourceMap,
    ) {
        let mut source_files = core::mem::replace(&mut self.source_files, Vec::new());
        for mut source_file in source_files.drain(..) {
            let filename = rustc_span::FileName::Real(rustc_span::RealFileName::LocalPath(
                std::path::PathBuf::from(source_file.path),
            ));
            let rustc_source_file = sm.get_source_file(&filename).unwrap();
            let start_pos = rustc_source_file.start_pos;
            for mut directive in source_file.directives.drain(..) {
                directive.set_span(start_pos);
                all_directives.push(directive);
            }
            for mut ghost_range in source_file.ghost_ranges.drain(..) {
                ghost_range.set_span(start_pos);
                all_ghost_ranges.push(ghost_range);
            }
        }
    }
}

struct FileLoader {
    read_only: bool,
    source_files: &'static std::sync::Mutex<SourceFiles>,
}

impl rustc_span::source_map::FileLoader for FileLoader {
    fn file_exists(&self, path: &std::path::Path) -> bool {
        path.exists()
    }

    fn read_file(&self, path: &std::path::Path) -> std::io::Result<String> {
        trace!("FileLoader::read_file({:?})", path);
        let contents = std::fs::read_to_string(&path)?;
        // Apparently, if the Rust library sources are installed, rustc reads them.
        // For now, this nasty hack skips those files. TODO: Find a way to keep rustc from reading dependencies' source files.
        if path.to_string_lossy().contains("toolchains") {
            Ok(contents)
        } else {
            let mut directives = Vec::new();
            let mut ghost_ranges = Vec::new();
            let preprocessed_contents =
                preprocessor::preprocess(contents.as_str(), self.read_only, &mut directives, &mut ghost_ranges);
            if self.read_only {
                assert_eq!(preprocessed_contents, contents);
            }
            self.source_files.lock().unwrap().push(SourceFile {
                path: path.into(),
                directives,
                ghost_ranges,
            });
            Ok(preprocessed_contents)
        }
    }

    fn read_binary_file(&self, path: &std::path::Path) -> std::io::Result<std::sync::Arc<[u8]>> {
        trace!("FileLoader::read_binary_file({:?})", path);
        let contents = std::fs::read(path)?;
        Ok(std::sync::Arc::from(contents))
    }
}

struct CompilerCalls {
    source_files: &'static std::sync::Mutex<SourceFiles>,
    preprocess_mode: PreprocessMode,
}

impl rustc_driver::Callbacks for CompilerCalls {
    // In this callback we override the mir_borrowck query.
    fn config(&mut self, config: &mut Config) {
        match &config.file_loader {
            None => {}
            Some(loader) => todo!(),
        }
        if self.preprocess_mode != PreprocessMode::DoNotPreprocess {
            config.file_loader = Some(Box::from(FileLoader {
                read_only: self.preprocess_mode == PreprocessMode::PreprocessReadOnly,
                source_files: self.source_files,
            }));
        }

        // assert!(config.override_queries.is_none());
        // config.override_queries = Some(override_queries);
    }

    // In this callback we trigger borrow checking of all functions and obtain
    // the result.
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        compiler.sess.psess.dcx().abort_if_errors();
        /*** Collecting Annotations */
        // TODO: Get comments from preprocessor

        /*** Collecting MIR bodies */
        trace!("Collecting MIR bodies");
        // Collect definition ids of bodies.
        let mut visitor = HirVisitor {
            tcx,
            structs: Vec::new(),
            trait_impls: Vec::new(),
            bodies: Vec::new(),
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

        let mut bodies = Vec::new();
        // Trigger borrow checking of all bodies.
        for (def_id, span) in visitor.bodies {
            //let _ = tcx.optimized_mir(def_id);
            let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
            if body.is_stolen() {
                trace!("Skipping body for {}; it's already been stolen", tcx.def_path_str(def_id));
            } else {
                bodies.push((
                    body.steal(),
                    span,
                ))
            }
        }

        // See what bodies were borrow checked.
        // let bodies_and_facts = get_bodies(tcx);

        // let bodies: Vec<_> = bodies_and_facts
        //     .iter()
        //     .map(|(def_path, body)| {
        //         assert!(body.input_facts.as_ref().unwrap().cfg_edge.len() > 0);
        //         debug!("We have body for {}", def_path);
        //         &body.body
        //     })
        //     .collect();

        let mut vf_mir_capnp_builder = vf_mir_builder::VfMirCapnpBuilder::new(tcx);
        let mut directives = Vec::new();
        let mut ghost_ranges = Vec::new();
        self.source_files.lock().unwrap().export_data(
            &mut directives,
            &mut ghost_ranges,
            tcx.sess.source_map(),
        );

        trace!("Ghost Ranges:\n{:#?}", ghost_ranges);
        for gr in &ghost_ranges {
            debug!("{:?}", gr.span());
        }
        vf_mir_capnp_builder.add_comments(&mut ghost_ranges);
        vf_mir_capnp_builder.set_directives(std::mem::replace(&mut directives, Vec::new()));
        vf_mir_capnp_builder.set_structs(visitor.structs);
        vf_mir_capnp_builder.set_trait_impls(visitor.trait_impls);
        vf_mir_capnp_builder.add_bodies(bodies);
        let msg_cpn = vf_mir_capnp_builder.build(compiler);
        capnp::serialize::write_message(&mut ::std::io::stdout(), msg_cpn.borrow_inner())
            .unwrap();
        Compilation::Stop
    }
}

// fn override_queries(_session: &Session, local: &mut rustc_middle::util::Providers) {
//     local.queries.mir_borrowck = mir_borrowck;
// }

// Since mir_borrowck does not have access to any other state, we need to use a
// thread-local for storing the obtained MIR bodies.
//
// Note: We are using 'static lifetime here, which is in general unsound.
// Unfortunately, that is the only lifetime allowed here. Our use is safe
// because we cast it back to `'tcx` before using.
// thread_local! {
//     pub static MIR_BODIES:
//         RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
//         RefCell::new(HashMap::new());
// }

// fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> rustc_middle::query::queries::mir_borrowck::ProvidedValue<'tcx> {
//     let body_with_facts = rustc_borrowck::consumers::get_body_with_borrowck_facts(
//         tcx,
//         def_id,
//         rustc_borrowck::consumers::ConsumerOptions::PoloniusOutputFacts
//     );
//     // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
//     let body_with_facts: BodyWithBorrowckFacts<'static> =
//         unsafe { std::mem::transmute(body_with_facts) };
//     MIR_BODIES.with(|state| {
//         let mut map = state.borrow_mut();
//         assert!(map.insert(def_id, body_with_facts).is_none());
//     });
//     let mut providers = rustc_middle::util::Providers::default();
//     rustc_borrowck::provide(&mut providers);
//     let original_mir_borrowck = providers.mir_borrowck;
//     original_mir_borrowck(tcx, def_id)
// }

struct TraitImplItemInfo {
    name: String,
    def_id: String,
}

struct TraitImplInfo {
    def_id: LocalDefId,
    span: Span,
    is_unsafe: bool,
    is_negative: bool,
    of_trait: rustc_hir::def_id::DefId,
    self_ty: rustc_hir::def_id::DefId,
    items: Vec<TraitImplItemInfo>,
}

/// Visitor that collects all body definition ids mentioned in the program.
struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    structs: Vec<LocalDefId>,
    trait_impls: Vec<TraitImplInfo>,
    bodies: Vec<(LocalDefId, Span)>,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for HirVisitor<'tcx> {

    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        match &item.kind {
            rustc_hir::ItemKind::Fn{ident, sig, generics, body, has_body} => {
                self.bodies.push((item.owner_id.def_id, sig.span))
            }
            // We cannot send DefId of a struct to optimize_mir query
            rustc_hir::ItemKind::Struct(..) => self.structs.push(item.owner_id.def_id),
            rustc_hir::ItemKind::Impl(impl_) => {
                if let Some(trait_ref) = &impl_.of_trait {
                    if let Some(of_trait) = trait_ref.trait_def_id() {
                        if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(
                            None,
                            self_ty_path,
                        )) = impl_.self_ty.kind
                        {
                            if let rustc_hir::def::Res::Def(
                                rustc_hir::def::DefKind::Struct,
                                self_ty,
                            ) = self_ty_path.res
                            {
                                let mut items = Vec::<TraitImplItemInfo>::new();
                                for item in impl_.items {
                                    items.push(
                                        TraitImplItemInfo {
                                            name: item.ident.to_string(),
                                            def_id: self.tcx.def_path_str(item.id.owner_id.to_def_id())
                                        }
                                    );
                                }
                                self.trait_impls.push(TraitImplInfo {
                                    def_id: item.owner_id.def_id,
                                    span: item.span,
                                    is_unsafe: impl_.safety == rustc_hir::Safety::Unsafe,
                                    is_negative: match impl_.polarity {
                                        rustc_hir::ImplPolarity::Negative(_) => true,
                                        _ => false,
                                    },
                                    of_trait,
                                    self_ty,
                                    items,
                                });
                            }
                        }
                    }
                }
            }
            _ => (),
        }
        rustc_hir::intravisit::walk_item(self, item);
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx rustc_hir::TraitItem<'tcx>) {
        if let rustc_hir::TraitItemKind::Fn(fn_sig, trait_fn) = &trait_item.kind {
            if let rustc_hir::TraitFn::Provided(_) = trait_fn {
                self.bodies.push((trait_item.owner_id.def_id, fn_sig.span));
            }
        }
        rustc_hir::intravisit::walk_trait_item(self, trait_item)
    }

    fn visit_impl_item(&mut self, impl_item: &'tcx rustc_hir::ImplItem<'tcx>) {
        if let rustc_hir::ImplItemKind::Fn(fn_sig, _) = impl_item.kind {
            self.bodies.push((impl_item.owner_id.def_id, fn_sig.span));
        }
        rustc_hir::intravisit::walk_impl_item(self, impl_item);
    }

    fn visit_foreign_item(&mut self, foreign_item: &'tcx rustc_hir::ForeignItem<'tcx>) {
        rustc_hir::intravisit::walk_foreign_item(self, foreign_item);
    }

    fn visit_fn(&mut self, fk: rustc_hir::intravisit::FnKind<'tcx>, fd: &'tcx rustc_hir::FnDecl<'tcx>, b: rustc_hir::BodyId, span: Span, id: LocalDefId) {
        match fk {
            rustc_hir::intravisit::FnKind::Closure => {
                trace!("Found closure {:?}", id);
                self.bodies.push((id, span));
            }
            _ => {}
        }
        rustc_hir::intravisit::walk_fn(self, fk, fd, b, id);
    }

}

/// Pull MIR bodies stored in the thread-local.
// fn get_bodies<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<(String, BodyWithBorrowckFacts<'tcx>)> {
//     MIR_BODIES.with(|state| {
//         let mut map = state.borrow_mut();
//         map.drain()
//             .map(|(def_id, body): (LocalDefId, BodyWithBorrowckFacts<'static>)| {
//                 let def_path = tcx.def_path(def_id.to_def_id());
//                 // SAFETY: For soundness we need to ensure that the bodies have
//                 // the same lifetime (`'tcx`), which they had before they were
//                 // stored in the thread local.
//                 let body_tcx: BodyWithBorrowckFacts<'tcx> = unsafe { std::mem::transmute(body) };
//                 (def_path.to_string_no_crate_verbose(), body_tcx)
//             })
//             .collect()
//     })
// }

mod vf_mir_builder {
    mod capnp_utils;
    use crate::preprocessor::GhostRange;
    use crate::preprocessor::GhostRangeKind;
    use crate::vf_mir_capnp::annotation as annot_cpn;
    use crate::vf_mir_capnp::body as body_cpn;
    use crate::vf_mir_capnp::hir as hir_cpn;
    use crate::vf_mir_capnp::ident as ident_cpn;
    use crate::vf_mir_capnp::mutability as mutability_cpn;
    use crate::vf_mir_capnp::predicate as predicate_cpn;
    use crate::vf_mir_capnp::span_data as span_data_cpn;
    use crate::vf_mir_capnp::symbol as symbol_cpn;
    use crate::vf_mir_capnp::ty as ty_cpn;
    use crate::vf_mir_capnp::unsafety as unsafety_cpn;
    use crate::vf_mir_capnp::vf_mir as vf_mir_cpn;
    use crate::vf_mir_capnp::visibility as visibility_cpn;
    use crate::vf_mir_capnp::variant_def as variant_def_cpn;
    use crate::vf_mir_capnp::operand as operand_cpn;
    use crate::vf_mir_capnp::rvalue as rvalue_cpn;
    use crate::vf_mir_capnp::statement as statement_cpn;
    use crate::vf_mir_capnp::terminator as terminator_cpn;
    use binary_op_data_cpn::bin_op as bin_op_cpn;
    use crate::vf_mir_capnp::basic_block as basic_block_cpn;
    use crate::vf_mir_capnp::basic_block_id as basic_block_id_cpn;
    use crate::vf_mir_capnp::const_operand as const_operand_cpn;
    use crate::vf_mir_capnp::mir_const as const_cpn;
    use crate::vf_mir_capnp::const_value as const_value_cpn;
    use crate::vf_mir_capnp::contract as contract_cpn;
    use crate::vf_mir_capnp::local_decl as local_decl_cpn;
    use crate::vf_mir_capnp::local_decl_id as local_decl_id_cpn;
    use crate::vf_mir_capnp::place as place_cpn;
    use crate::vf_mir_capnp::scalar as scalar_cpn;
    use crate::vf_mir_capnp::source_info as source_info_cpn;
    use crate::vf_mir_capnp::var_debug_info as var_debug_info_cpn;
    use crate::vf_mir_capnp::real_file_name as real_file_name_cpn;
    use hir_cpn::generics as hir_generics_cpn;
    use hir_generic_param_cpn::generic_param_kind as hir_generic_param_kind_cpn;
    use hir_generic_param_cpn::param_name as hir_generic_param_name_cpn;
    use hir_generics_cpn::generic_param as hir_generic_param_cpn;
    use crate::vf_mir_capnp::char_pos as char_pos_cpn;
    use crate::vf_mir_capnp::source_file as source_file_cpn;
    use mir::HasLocalDecls;
    use crate::vf_mir_capnp::place_elem as place_element_cpn;
    use ref_data_cpn::borrow_kind as borrow_kind_cpn;
    use rustc_ast::util::comments::Comment;
    use rustc_hir as hir;
    use rustc_interface::interface::Compiler;
    use rustc_middle::bug;
    use rustc_middle::mir::interpret::AllocRange;
    use rustc_middle::mir::UnwindAction;
    use rustc_middle::ty;
    use rustc_middle::ty::GenericParamDef;
    use rustc_middle::ty::GenericParamDefKind;
    use rustc_middle::{mir, ty::TyCtxt};
    use rustc_span::source_map::Spanned;
    use rustc_span::Span;
    use crate::vf_mir_capnp::aggregate_kind as aggregate_kind_cpn;
    use rvalue_cpn::binary_op_data as binary_op_data_cpn;
    use rvalue_cpn::ref_data as ref_data_cpn;
    use rvalue_cpn::unary_op_data as unary_op_data_cpn;
    use crate::vf_mir_capnp::file_name as file_name_cpn;
    use crate::vf_mir_capnp::loc as loc_cpn;
    use crate::vf_mir_capnp::statement_kind as statement_kind_cpn;
    use std::collections::LinkedList;
    use std::sync::Arc;
    use crate::vf_mir_capnp::switch_targets as switch_targets_cpn;
    use crate::vf_mir_capnp::terminator_kind as terminator_kind_cpn;
    use terminator_kind_cpn::fn_call_data as fn_call_data_cpn;
    use crate::vf_mir_capnp::unwind_action as unwind_action_cpn;
    use terminator_kind_cpn::switch_int_data as switch_int_data_cpn;
    use tracing::{debug, trace};
    use crate::vf_mir_capnp::adt_def as adt_def_cpn;
    use crate::vf_mir_capnp::adt_def_id as adt_def_id_cpn;
    use crate::vf_mir_capnp::adt_kind as adt_kind_cpn;
    use ty_kind_cpn::adt_ty as adt_ty_cpn;
    use crate::vf_mir_capnp::ty_const as ty_const_cpn;
    use crate::vf_mir_capnp::const_kind as const_kind_cpn;
    use crate::vf_mir_capnp::val_tree as val_tree_cpn;
    use crate::vf_mir_capnp::scalar_int as scalar_int_cpn;
    use ty_kind_cpn::fn_def_ty as fn_def_ty_cpn;
    use crate::vf_mir_capnp::generic_arg as gen_arg_cpn;
    use crate::vf_mir_capnp::int_ty as int_ty_cpn;
    use ty_kind_cpn::raw_ptr_ty as raw_ptr_ty_cpn;
    use ty_kind_cpn::ref_ty as ref_ty_cpn;
    use crate::vf_mir_capnp::region as region_cpn;
    use crate::vf_mir_capnp::ty_kind as ty_kind_cpn;
    use crate::vf_mir_capnp::u_int_ty as u_int_ty_cpn;
    use unary_op_data_cpn::un_op as un_op_cpn;
    use crate::vf_mir_capnp::var_debug_info_contents as var_debug_info_contents_cpn;
    use variant_def_cpn::field_def as field_def_cpn;

    struct Module {
        name: String,
        header_span: rustc_span::Span,
        body_span: rustc_span::Span,
        submodules: Vec<Box<Module>>,
        ghost_decl_batches: LinkedList<Box<GhostRange>>,
    }

    fn collect_submodules<'tcx, 'a>(
        tcx: TyCtxt<'tcx>,
        annots: &'a mut LinkedList<Box<GhostRange>>,
        mod_id: rustc_span::def_id::LocalModDefId,
    ) -> Vec<Box<Module>> {
        struct ModVisitor<'tcx, 'a> {
            tcx: TyCtxt<'tcx>,
            submodules: Vec<Box<Module>>,
            annots: &'a mut LinkedList<Box<GhostRange>>,
        }
        impl<'tcx, 'a> rustc_hir::intravisit::Visitor<'tcx> for ModVisitor<'tcx, 'a> {
            fn visit_mod(
                &mut self,
                m: &'tcx rustc_hir::Mod<'tcx>,
                header_span: rustc_span::Span,
                n: rustc_hir::HirId,
            ) {
                let name = self.tcx.hir_ident(n).as_str().into();
                let mut body_span = m.spans.inner_span;
                if Arc::as_ptr(&self.tcx.sess.source_map().lookup_source_file(header_span.lo())) ==
                    Arc::as_ptr(&self.tcx.sess.source_map().lookup_source_file(body_span.lo())) {
                    body_span = header_span.to(body_span);
                }
                let mut mod_annots: LinkedList<Box<GhostRange>> = self
                    .annots
                    .extract_if(|annot| body_span.contains(annot.span().unwrap()))
                    .collect();
                let mod_submodules = collect_submodules(
                    self.tcx,
                    &mut mod_annots,
                    rustc_hir::def_id::LocalModDefId::new_unchecked(n.expect_owner().def_id),
                );
                self.submodules.push(Box::new(Module {
                    name,
                    header_span,
                    body_span,
                    submodules: mod_submodules,
                    ghost_decl_batches: mod_annots,
                }));
            }
        }
        let mut visitor = ModVisitor {
            tcx,
            submodules: Vec::new(),
            annots,
        };
        tcx.hir_visit_item_likes_in_module(mod_id, &mut visitor);
        visitor.submodules
    }

    #[derive(Clone, Copy)]
    enum PlaceKind { MutableRef, SharedRef, Other }

    enum EncKind<'tcx, 'a> {
        Body(&'a mir::Body<'tcx>),
        Adt,
        Other,
    }
    struct EncCtx<'tcx, 'a> {
        req_adts: Vec<ty::AdtDef<'tcx>>,
        tcx: TyCtxt<'tcx>,
        mode: EncKind<'tcx, 'a>,
        annots: LinkedList<Box<GhostRange>>,
        mut_annots: Vec<rustc_span::BytePos>,
    }

    impl<'tcx, 'a> EncCtx<'tcx, 'a> {
        pub fn new(
            tcx: TyCtxt<'tcx>,
            mode: EncKind<'tcx, 'a>,
            annots: LinkedList<Box<GhostRange>>,
            mut_annots: Vec<rustc_span::BytePos>,
        ) -> Self {
            Self {
                req_adts: Vec::new(),
                tcx,
                mode,
                annots,
                mut_annots,
            }
        }
        pub fn add_req_adt(&mut self, adt: ty::AdtDef<'tcx>) {
            /* Todo @Nima: It is necessary to encode the dependency between the required definitions.
                Because the order of definitions will matter in most of the analyzers.
            */
            self.req_adts.push(adt);
        }
        pub fn get_req_adts(&self) -> &Vec<ty::AdtDef<'tcx>> {
            &self.req_adts
        }
        pub fn body(&self) -> &'a mir::Body<'tcx> {
            match self.mode {
                EncKind::Body(body) => body,
                _ => bug!(),
            }
        }
    }

    pub struct VfMirCapnpBuilder<'tcx> {
        tcx: TyCtxt<'tcx>,
        directives: Vec<Box<GhostRange>>,
        structs: Vec<rustc_span::def_id::LocalDefId>,
        trait_impls: Vec<super::TraitImplInfo>,
        bodies: Vec<(mir::Body<'tcx>, Span)>,
        annots: LinkedList<Box<GhostRange>>,
    }

    impl<'tcx: 'a, 'a> VfMirCapnpBuilder<'tcx> {
        pub fn new(tcx: TyCtxt<'tcx>) -> VfMirCapnpBuilder<'tcx> {
            VfMirCapnpBuilder {
                tcx,
                directives: Vec::new(),
                structs: Vec::new(),
                trait_impls: Vec::new(),
                bodies: Vec::new(),
                annots: LinkedList::new(),
            }
        }

        pub(super) fn set_directives(&mut self, directives: Vec<Box<GhostRange>>) {
            self.directives = directives;
        }

        pub fn add_comments(&mut self, annots: &mut Vec<Box<GhostRange>>) {
            self.annots.extend(
                annots
                    .extract_if(.., |annot| !annot.is_dummy())
                    .collect::<LinkedList<_>>(),
            );
        }

        pub(super) fn set_structs(&mut self, structs: Vec<rustc_span::def_id::LocalDefId>) {
            self.structs = structs;
        }

        pub(super) fn set_trait_impls(&mut self, trait_impls: Vec<super::TraitImplInfo>) {
            self.trait_impls = trait_impls;
        }

        pub fn add_bodies(&mut self, bodies: Vec<(mir::Body<'tcx>, Span)>) {
            self.bodies = bodies;
        }

        pub fn build(
            mut self,
            compiler: &Compiler,
        ) -> ::capnp::message::TypedBuilder<vf_mir_cpn::Owned> {
            let mut msg_cpn = ::capnp::message::TypedBuilder::<vf_mir_cpn::Owned>::new_default();
            let mut vf_mir_cpn = msg_cpn.init_root();
            vf_mir_cpn.set_target_triple(&compiler.sess.target.llvm_target);
            vf_mir_cpn.set_pointer_width(compiler.sess.target.pointer_width.try_into().unwrap());
            self.encode_trait_impls(&mut vf_mir_cpn);
            self.encode_mir(vf_mir_cpn);
            msg_cpn
        }

        fn encode_trait_impls(&mut self, vf_mir_cpn: &mut vf_mir_cpn::Builder<'_>) {
            let mut enc_ctx = EncCtx::new(self.tcx, EncKind::Other, LinkedList::new(), Vec::new());
            vf_mir_cpn.fill_trait_impls(&self.trait_impls, |mut trait_impl_cpn, trait_impl| {
                trace!("Encoding trait impl");
                let trait_ref = self
                    .tcx
                    .impl_trait_ref(trait_impl.def_id)
                    .unwrap()
                    .skip_binder();
                trait_impl_cpn.fill_gen_args(trait_ref.args, |gen_arg_cpn, gen_arg| {
                    Self::encode_gen_arg(enc_ctx.tcx, &mut enc_ctx, gen_arg, gen_arg_cpn);
                });
                Self::encode_span_data(
                    self.tcx,
                    &trait_impl.span.data(),
                    trait_impl_cpn.reborrow().init_span(),
                );
                trait_impl_cpn.set_is_unsafe(trait_impl.is_unsafe);
                trait_impl_cpn.set_is_negative(trait_impl.is_negative);
                trait_impl_cpn.fill_generics(
                    &self.tcx.generics_of(trait_impl.def_id).own_params,
                    |generic_param_cpn, generic_param| {
                        Self::encode_generic_param_def(generic_param, generic_param_cpn);
                    },
                );
                trait_impl_cpn.fill_predicates(
                    self.tcx.predicates_of(trait_impl.def_id).predicates,
                    |pred_cpn, pred| {
                        Self::encode_predicate(&mut enc_ctx, pred, pred_cpn);
                    },
                );
                trait_impl_cpn.set_of_trait(&self.tcx.def_path_str(trait_impl.of_trait));
                trait_impl_cpn.set_self_ty(&self.tcx.def_path_str(trait_impl.self_ty));
                trait_impl_cpn.fill_items(&trait_impl.items, |mut item_cpn, item| {
                    item_cpn.set_name(&item.name); 
                    item_cpn.set_def_id(&item.def_id);
                });
            });
        }

        fn encode_traits(
            &mut self,
            req_adt_defs: &mut Vec<ty::AdtDef<'tcx>>,
            mut vf_mir_cpn: vf_mir_cpn::Builder<'_>,
        ) {
            let mut enc_ctx = EncCtx::new(self.tcx, EncKind::Adt, LinkedList::new(), Vec::new());
            let mut traits_cpn = vf_mir_cpn.reborrow().init_traits();
            for trait_def_id in self.tcx.all_traits() {
                if trait_def_id.krate != rustc_hir::def_id::LOCAL_CRATE {
                    break; // We assume that the local crate's traits come first.
                }
                let mut traits_cons_cpn = traits_cpn.init_cons();
                let mut trait_cpn = traits_cons_cpn.reborrow().init_h();
                let name = self.tcx.def_path_str(trait_def_id);
                trait_cpn.set_name(&name);
                let mut required_fns_cpn = trait_cpn.reborrow().init_required_fns();
                for item in self
                    .tcx
                    .associated_items(trait_def_id)
                    .in_definition_order()
                {
                    if item.kind.as_def_kind() == rustc_hir::def::DefKind::AssocFn {
                        let hir_item = self.tcx.hir_expect_trait_item(item.def_id.expect_local());
                        match &hir_item.kind {
                            hir::TraitItemKind::Fn(fn_sig, trait_fn) => {
                                if let hir::TraitFn::Required(arg_names) = trait_fn {
                                    let polysig = self.tcx.fn_sig(item.def_id);
                                    let sig0 = polysig.skip_binder();
                                    let sig = sig0.skip_binder();
                                    let mut required_fns_cons_cpn = required_fns_cpn.init_cons();
                                    let mut required_fn_cpn =
                                        required_fns_cons_cpn.reborrow().init_h();
                                    required_fn_cpn.set_name(&item.name.to_string());
                                    Self::encode_span_data(
                                        self.tcx,
                                        &hir_item.ident.span.data(),
                                        required_fn_cpn.reborrow().init_name_span(),
                                    );
                                    Self::encode_unsafety(
                                        match fn_sig.header.safety {
                                            hir::HeaderSafety::SafeTargetFeatures => todo!(),
                                            hir::HeaderSafety::Normal(safety) => safety,
                                        },
                                        required_fn_cpn.reborrow().init_unsafety(),
                                    );
                                    required_fn_cpn.fill_lifetime_params(
                                        sig0.bound_vars().iter().map(|bound_var| match bound_var {
                                            ty::BoundVariableKind::Ty(bound_ty_kind) => todo!(),
                                            ty::BoundVariableKind::Region(bound_region_kind) => {
                                                match bound_region_kind {
                                                    ty::BoundRegionKind::Anon => todo!(),
                                                    ty::BoundRegionKind::Named(
                                                        def_id,
                                                        symbol,
                                                    ) => symbol.to_string(),
                                                    ty::BoundRegionKind::ClosureEnv => todo!(),
                                                }
                                            }
                                            ty::BoundVariableKind::Const => todo!(),
                                        }),
                                    );
                                    required_fn_cpn.fill_inputs(
                                        sig.inputs(),
                                        |input_cpn, input| {
                                            Self::encode_ty(
                                                self.tcx,
                                                &mut enc_ctx,
                                                *input,
                                                input_cpn,
                                            );
                                        },
                                    );
                                    Self::encode_ty(
                                        self.tcx,
                                        &mut enc_ctx,
                                        sig.output(),
                                        required_fn_cpn.reborrow().init_output(),
                                    );
                                    required_fn_cpn
                                        .fill_arg_names(arg_names.iter().map(|n| n.as_ref().map(|i| i.as_str()).unwrap_or("_")));
                                    let contract: Vec<Box<GhostRange>> = self
                                        .annots
                                        .extract_if(|annot| {
                                            annot.end_of_preceding_token.byte_pos
                                                == hir_item.span.hi().0
                                        })
                                        .collect();
                                    required_fn_cpn.fill_contract(&contract, |annot_cpn, annot| {
                                        Self::encode_annotation(self.tcx, annot, annot_cpn);
                                    });
                                    required_fns_cpn = required_fns_cons_cpn.init_t();
                                }
                            }
                            _ => {}
                        }
                    }
                }
                traits_cpn = traits_cons_cpn.init_t();
            }
            req_adt_defs.extend(enc_ctx.get_req_adts());
        }

        fn encode_module(
            tcx: TyCtxt<'tcx>,
            mut module_cpn: crate::vf_mir_capnp::module::Builder<'_>,
            module: &Box<Module>,
        ) {
            module_cpn.set_name(&module.name);
            Self::encode_span_data(
                tcx,
                &module.header_span.data(),
                module_cpn.reborrow().init_header_span(),
            );
            Self::encode_span_data(
                tcx,
                &module.body_span.data(),
                module_cpn.reborrow().init_body_span(),
            );
            module_cpn
                .reborrow()
                .fill_submodules(&module.submodules, |module_cpn, module| {
                    Self::encode_module(tcx, module_cpn, module);
                });
            module_cpn.reborrow().fill_ghost_decl_batches(
                &module.ghost_decl_batches,
                |annot_cpn, annot| {
                    Self::encode_annotation(tcx, annot, annot_cpn);
                },
            );
        }

        fn encode_mir(&mut self, mut vf_mir_cpn: vf_mir_cpn::Builder<'_>) {
            let mut req_adt_defs = Vec::new();

            for struct_did in &self.structs {
                req_adt_defs.push(self.tcx.adt_def(struct_did.to_def_id()));
            }

            // Encode traits (consumes annotations)
            self.encode_traits(&mut req_adt_defs, vf_mir_cpn.reborrow());

            vf_mir_cpn.fill_bodies(&self.bodies, |mut body_cpn, (body, span)| {
                Self::encode_span_data(
                    self.tcx,
                    &span.data(),
                    body_cpn.reborrow().init_fn_sig_span(),
                );
                let body_span = body.span.data();
                let mut annots = self
                    .annots
                    .extract_if(|annot| {
                        body_span.contains(
                            annot
                                .span()
                                .expect("Dummy annot found during serialization")
                                .data(),
                        )
                    })
                    .collect::<LinkedList<_>>();
                let mut_annots = annots.extract_if(|annot| {
                    annot.kind == GhostRangeKind::Mut
                }).map(|annot| {
                    trace!("Found mut annotation: {:?}", annot);
                    annot.span().unwrap().data().hi
                }).collect::<Vec<_>>();
                let mut enc_ctx = EncCtx::new(self.tcx, EncKind::Body(body), annots, mut_annots);
                Self::encode_body(&mut enc_ctx, body_cpn);
                req_adt_defs.extend(enc_ctx.get_req_adts());
            });

            // Encode directives
            vf_mir_cpn.fill_directives(&self.directives, |directive_cpn, directive| {
                Self::encode_annotation(self.tcx, directive, directive_cpn);
            });

            // Encode modules
            let modules = collect_submodules(
                self.tcx,
                &mut self.annots,
                rustc_hir::def_id::LocalModDefId::CRATE_DEF_ID,
            );
            vf_mir_cpn.fill_modules(&modules, |module_cpn, module| {
                Self::encode_module(self.tcx, module_cpn, module);
            });

            // Encode Ghost Declarations
            let ghost_decl_batches = self
                .annots
                .extract_if(|annot| {
                    let annot_span = annot
                        .span()
                        .expect("Dummy annotation found during serialization");
                    if let Some((body, span)) = self
                        .bodies
                        .iter()
                        .find(|(body, span)| body.span.overlaps(annot_span))
                    {
                        panic!(
                            "Overlapping Ghost Declaration Block at {:?} and Function at {:?}",
                            annot_span, body.span
                        )
                    }
                    true
                })
                .collect::<LinkedList<_>>();
            vf_mir_cpn.fill_ghost_decl_batches(ghost_decl_batches, |gh_decl_b_cpn, gh_decl_b| {
                Self::encode_annotation(self.tcx, &gh_decl_b, gh_decl_b_cpn);
            });

            // Encode Required Definitions
            let mut adt_defs_cpn = vf_mir_cpn.init_adt_defs();
            let mut encoded_adt_defs = Vec::new();
            while !req_adt_defs.is_empty() {
                let it = req_adt_defs.into_iter();
                req_adt_defs = Vec::new();
                for adt_def in it {
                    if adt_def.is_unsafe_cell()
                        || adt_def.is_manually_drop()
                        || !adt_def.did().is_local()
                    {
                        continue;
                    }
                    match encoded_adt_defs
                        .iter()
                        .find(|&&enc_adt_def| enc_adt_def == adt_def)
                    {
                        Option::None => {
                            let mut adt_defs_cons_cpn = adt_defs_cpn.init_cons();
                            let adt_def_cpn = adt_defs_cons_cpn.reborrow().init_h();
                            let mut enc_ctx =
                                EncCtx::new(self.tcx, EncKind::Adt, LinkedList::new(), Vec::new());
                            Self::encode_adt_def(self.tcx, &mut enc_ctx, &adt_def, adt_def_cpn);
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
            adt_def: &ty::AdtDef<'tcx>,
            mut adt_def_cpn: adt_def_cpn::Builder<'_>,
        ) {
            debug!("Encoding ADT definition {:?}", adt_def);
            let id_cpn = adt_def_cpn.reborrow().init_id();
            Self::encode_adt_def_id(enc_ctx, adt_def.did(), id_cpn);
            let mut variant_index = 0;
            adt_def_cpn.fill_variants(adt_def.variants(), |variant_cpn, variant| {
                Self::encode_variant_def(tcx, enc_ctx, variant_index, variant, variant_cpn);
                variant_index += 1;
            });
            let kind_cpn = adt_def_cpn.reborrow().init_kind();
            Self::encode_adt_kind(adt_def.adt_kind(), kind_cpn);
            let span_cpn = adt_def_cpn.reborrow().init_span();
            let span = tcx.def_span(adt_def.did());
            Self::encode_span_data(tcx, &span.data(), span_cpn);
            if adt_def.did().is_local() {
                if let rustc_hir::Node::Item(item) = tcx.hir_node_by_def_id(adt_def.did().expect_local()) {
                    let def_span = item.span.data();
                    Self::encode_span_data(tcx, &def_span, adt_def_cpn.reborrow().init_def_span());
                }
            }
            let vis_cpn = adt_def_cpn.reborrow().init_vis();
            let vis = tcx.visibility(adt_def.did());
            Self::encode_visibility(vis, vis_cpn);
            let is_local = adt_def.did().is_local();
            adt_def_cpn.set_is_local(is_local);
            debug!(
                "Adt def {:?} Visibility:{:?} Local:{}",
                adt_def, vis, is_local
            );
            let hir_gens_cpn = adt_def_cpn.reborrow().init_hir_generics();
            let hir_gens = tcx
                .hir_get_generics(adt_def.did().expect_local())
                .expect(&format!("Failed to get HIR generics data"));
            Self::encode_hir_generics(enc_ctx, hir_gens, hir_gens_cpn);

            let variances = tcx.variances_of(adt_def.did());
            let mut variances_cpn = adt_def_cpn.reborrow().init_variances(variances.len());
            for (i, variance) in variances.iter().enumerate() {
                let variance_cpn = match variance {
                    rustc_middle::ty::Variance::Invariant => crate::vf_mir_capnp::Variance::Invariant,
                    rustc_middle::ty::Variance::Covariant => crate::vf_mir_capnp::Variance::Covariant,
                    rustc_middle::ty::Variance::Contravariant => crate::vf_mir_capnp::Variance::Contravariant,
                    rustc_middle::ty::Variance::Bivariant => crate::vf_mir_capnp::Variance::Bivariant,
                };
                variances_cpn.set(i as u32, variance_cpn);
            }

            let predicates = tcx.predicates_of(adt_def.did()).predicates;
            adt_def_cpn.fill_predicates(predicates, |pred_cpn, pred| {
                Self::encode_predicate(enc_ctx, pred, pred_cpn);
            });
            adt_def_cpn.set_implements_drop(adt_def.has_dtor(tcx));
            adt_def_cpn.set_is_repr_c(adt_def.repr().c());
        }

        fn encode_adt_kind(adt_kind: ty::AdtKind, mut adt_kind_cpn: adt_kind_cpn::Builder<'_>) {
            match adt_kind {
                ty::AdtKind::Struct => adt_kind_cpn.set_struct_kind(()),
                ty::AdtKind::Union => adt_kind_cpn.set_union_kind(()),
                ty::AdtKind::Enum => adt_kind_cpn.set_enum_kind(()),
            }
        }

        fn encode_variant_def(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            variant_index: u32,
            vdef: &ty::VariantDef,
            mut vdef_cpn: variant_def_cpn::Builder<'_>,
        ) {
            vdef_cpn.set_name(vdef.name.as_str());
            Self::encode_span_data(
                tcx,
                &tcx.def_span(vdef.def_id).data(),
                vdef_cpn.reborrow().init_span(),
            );
            vdef_cpn.fill_fields(&vdef.fields, |field_cpn, field| {
                Self::encode_field_def(tcx, enc_ctx, field, field_cpn);
            });
            match vdef.discr {
                ty::VariantDiscr::Explicit(_) => todo!(),
                ty::VariantDiscr::Relative(discr) => {
                    if discr != variant_index {
                        todo!()
                    }
                }
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
            let ty = tcx.type_of(fdef.did).instantiate_identity();
            Self::encode_ty(tcx, enc_ctx, ty, ty_cpn);
            let vis_cpn = fdef_cpn.reborrow().init_vis();
            Self::encode_visibility(fdef.vis, vis_cpn);
            let span_cpn = fdef_cpn.init_span();
            let span = tcx.def_span(fdef.did);
            Self::encode_span_data(tcx, &span.data(), span_cpn);
        }

        fn encode_visibility(
            vis: ty::Visibility<rustc_hir::def_id::DefId>,
            mut vis_cpn: visibility_cpn::Builder<'_>,
        ) {
            match vis {
                ty::Visibility::Public => vis_cpn.set_public(()),
                ty::Visibility::Restricted(_did) => vis_cpn.set_restricted(()),
            }
        }

        fn encode_predicate(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            pred: &(ty::Clause<'tcx>, rustc_span::Span),
            mut pred_cpn: predicate_cpn::Builder<'_>,
        ) {
            match pred.0.kind().skip_binder() {
                ty::ClauseKind::RegionOutlives(outlives_pred) => {
                    let mut outlives_cpn = pred_cpn.init_outlives();
                    Self::encode_region(outlives_pred.0, outlives_cpn.reborrow().init_region1());
                    Self::encode_region(outlives_pred.1, outlives_cpn.reborrow().init_region2());
                }
                ty::ClauseKind::Trait(trait_pred) => {
                    let bound_vars = pred.0.kind().bound_vars();
                    let mut trait_cpn = pred_cpn.init_trait();
                    trait_cpn.fill_bound_regions(bound_vars.iter().map(|v| {
                        match v {
                            ty::BoundVariableKind::Region(ty::BoundRegionKind::Named(def_id, symbol)) => {
                                if symbol.as_str() == "'_" {
                                    Self::anonymous_late_bound_lifetime_name(def_id.index.as_usize())
                                } else {
                                    symbol.as_str().to_string()
                                }
                            }
                            _ => todo!()
                        }
                    }));
                    trait_cpn.set_def_id(&enc_ctx.tcx.def_path_str(trait_pred.trait_ref.def_id));
                    trait_cpn.fill_args(trait_pred.trait_ref.args, |arg_cpn, arg| {
                        Self::encode_gen_arg(enc_ctx.tcx, enc_ctx, arg, arg_cpn);
                    });
                }
                ty::ClauseKind::Projection(projection_pred) => {
                    let bound_vars = pred.0.kind().bound_vars();
                    let mut proj_cpn = pred_cpn.init_projection();
                    proj_cpn.fill_bound_regions(bound_vars.iter().map(|v| {
                        match v {
                            ty::BoundVariableKind::Region(ty::BoundRegionKind::Named(def_id, symbol)) => {
                                if symbol.as_str() == "'_" {
                                    Self::anonymous_late_bound_lifetime_name(def_id.index.as_usize())
                                } else {
                                    symbol.as_str().to_string()
                                }
                            }
                            _ => todo!()
                        }
                    }));
                    let mut proj_term_cpn = proj_cpn.reborrow().init_projection_term();
                    proj_term_cpn.set_def_id(&enc_ctx.tcx.def_path_str(projection_pred.projection_term.def_id));
                    proj_term_cpn.fill_args(projection_pred.projection_term.args, |arg_cpn, arg| {
                        Self::encode_gen_arg(enc_ctx.tcx, enc_ctx, arg, arg_cpn);
                    });
                    let term_cpn = proj_cpn.reborrow().init_term();
                    match projection_pred.term.unpack() {
                        ty::TermKind::Ty(ty) =>
                            Self::encode_ty(enc_ctx.tcx, enc_ctx, ty, term_cpn.init_ty()),
                        ty::TermKind::Const(const_) =>
                            Self::encode_typesystem_constant(enc_ctx.tcx, enc_ctx, &const_, term_cpn.init_const()),
                    }
                }
                _ => pred_cpn.set_ignored(()),
            }
        }

        fn anonymous_early_bound_lifetime_name(index: u32) -> String {
            format!("'_{}", index)
        }

        fn anonymous_late_bound_lifetime_name(index: usize) -> String {
            format!("'__{}", index)
        }

        fn encode_generic_param_def(
            generic_param: &GenericParamDef,
            mut generic_param_cpn: crate::vf_mir_capnp::generic_param_def::Builder<'_>,
        ) {
            if generic_param.is_anonymous_lifetime() {
                generic_param_cpn.set_name(&Self::anonymous_early_bound_lifetime_name(generic_param.index));
            } else {
                generic_param_cpn.set_name(generic_param.name.as_str());
            }
            let mut kind_cpn = generic_param_cpn.init_kind();
            match generic_param.kind {
                GenericParamDefKind::Lifetime => kind_cpn.set_lifetime(()),
                GenericParamDefKind::Type { .. } => kind_cpn.set_type(()),
                GenericParamDefKind::Const { .. } => kind_cpn.set_const(()),
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
            let is_closure = match kind {
                hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                    let mut def_kind_cpn = body_cpn.reborrow().init_def_kind();
                    def_kind_cpn.set_fn(());
                    if kind == hir::def::DefKind::AssocFn {
                        let assoc_item = tcx.associated_item(def_id);
                        if assoc_item.container == ty::AssocItemContainer::Trait {
                            body_cpn.set_is_trait_fn(true);
                        } else {
                            if let Some(trait_fn) = assoc_item.trait_item_def_id {
                                if let Some(trait_did) = tcx.trait_of_item(trait_fn) {
                                    if let Some(drop_did) = tcx.lang_items().drop_trait() {
                                        if trait_did == drop_did {
                                            body_cpn.set_is_drop_fn(true);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    false
                }
                hir::def::DefKind::Closure => {
                    let mut def_kind_cpn = body_cpn.reborrow().init_def_kind();
                    def_kind_cpn.set_closure(());
                    true
                }
                _ => std::todo!("Unsupported definition kind"),
            };

            let def_path = tcx.def_path_str(def_id);
            body_cpn.set_def_path(&def_path);

            let parent_module = tcx.parent_module_from_def_id(def_id.expect_local());
            if parent_module != rustc_span::def_id::LocalModDefId::CRATE_DEF_ID {
                body_cpn.set_module_def_path(&tcx.def_path_str(parent_module.to_def_id()));
            }

            if !is_closure {
                Self::encode_unsafety(
                    tcx.fn_sig(def_id).skip_binder().safety(),
                    body_cpn.reborrow().init_unsafety(),
                );
            }

            if let Some(impl_did) = tcx.impl_of_method(def_id) {
                let impl_hir_gens = tcx.hir_get_generics(impl_did.expect_local()).unwrap();
                let impl_hir_generics_cpn = body_cpn.reborrow().init_impl_block_hir_generics();
                let impl_hir_generics_some_cpn = impl_hir_generics_cpn.init_something();
                Self::encode_hir_generics(enc_ctx, impl_hir_gens, impl_hir_generics_some_cpn);

                let impl_gens = tcx.generics_of(impl_did);
                body_cpn.reborrow().fill_impl_block_generics(
                    &impl_gens.own_params,
                    |generic_param_cpn, generic_param| {
                        Self::encode_generic_param_def(generic_param, generic_param_cpn);
                    },
                );

                let impl_preds = tcx.predicates_of(impl_did).predicates;
                body_cpn.fill_impl_block_predicates(impl_preds, |pred_cpn, pred| {
                    Self::encode_predicate(enc_ctx, pred, pred_cpn);
                });
            }

            if !is_closure {
                let hir_gens_cpn = body_cpn.reborrow().init_hir_generics();
                let hir_gens = tcx
                    .hir_get_generics(def_id.expect_local())
                    .expect(&format!("Failed to get HIR generics data"));
                Self::encode_hir_generics(enc_ctx, hir_gens, hir_gens_cpn);
            }

            let generics = tcx.generics_of(def_id);
            body_cpn.reborrow().fill_generics(
                &generics.own_params,
                |generic_param_cpn, generic_param| {
                    Self::encode_generic_param_def(generic_param, generic_param_cpn);
                },
            );

            let predicates = tcx.predicates_of(def_id).predicates;
            trace!("Encoding predicates: {:?}", predicates);
            body_cpn
                .reborrow()
                .fill_predicates(predicates, |pred_cpn, pred| {
                    Self::encode_predicate(enc_ctx, pred, pred_cpn);
                });

            if !is_closure {
                let contract_cpn = body_cpn.reborrow().init_contract();
                let body_contract_span = crate::span_utils::body_contract_span(tcx, body);
                let contract_annots = enc_ctx
                    .annots
                    .extract_if(|annot| {
                        body_contract_span.contains(annot.span().expect("Dummy span").data())
                    })
                    .collect::<LinkedList<_>>();
                Self::encode_contract(tcx, contract_annots, &body_contract_span, contract_cpn);
            }

            let local_decls_count = body.local_decls().len();
            
            if !is_closure {
                let polysig = tcx.fn_sig(def_id);
                let sig0 = polysig.skip_binder();
                let sig = sig0.skip_binder();
                Self::encode_ty(
                    tcx,
                    enc_ctx,
                    sig.output(),
                    body_cpn.reborrow().init_output(),
                );
                body_cpn.fill_inputs(sig.inputs(), |input_cpn, input| {
                    Self::encode_ty(tcx, enc_ctx, *input, input_cpn);
                });
                assert!(
                    local_decls_count > sig.inputs().len() as usize,
                    "Local declarations of {} are not more than its args",
                    def_path
                );
            }

            body_cpn.fill_local_decls(
                body.local_decls().iter_enumerated(),
                |local_decl_cpn, (local_decl_idx, local_decl)| {
                    Self::encode_local_decl(
                        tcx,
                        enc_ctx,
                        local_decl_idx,
                        local_decl,
                        local_decl_cpn,
                    );
                },
            );

            body_cpn.fill_basic_blocks(
                body.basic_blocks.iter_enumerated(),
                |basic_block_cpn, (basic_block_idx, basic_block)| {
                    Self::encode_basic_block(
                        tcx,
                        enc_ctx,
                        basic_block_idx,
                        basic_block,
                        basic_block_cpn,
                    );
                },
            );

            let span_cpn = body_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, &body.span.data(), span_cpn);

            let imp_span_cpn = body_cpn.reborrow().init_imp_span();
            let imp_span_data = crate::span_utils::body_imp_span(tcx, body);
            Self::encode_span_data(tcx, &imp_span_data, imp_span_cpn);

            body_cpn.fill_var_debug_info(&body.var_debug_info, |vdi_cpn, vdi| {
                Self::encode_var_debug_info(tcx, enc_ctx, vdi, vdi_cpn);
            });

            let mut ghost_stmts = enc_ctx
                .annots
                .extract_if(|annot| {
                    imp_span_data.contains(annot.span().expect("Dummy ghost range").data())
                })
                .collect::<LinkedList<_>>();
            assert!(
                enc_ctx.annots.is_empty(),
                "There are annotations for {} that are neither in contract nor in the body: {:?}",
                def_path, enc_ctx.annots
            );

            let ghost_decl_blocks = ghost_stmts
                .extract_if(|annot| annot.kind == GhostRangeKind::BlockDecls)
                .collect::<LinkedList<_>>();
            for b in &ghost_decl_blocks {
                if b.kind == GhostRangeKind::GenericArgs {
                    panic!(
                        "Ghost generic args list not matched to function call at {:?}",
                        b.span()
                    );
                }
            }
            body_cpn.fill_ghost_stmts(&ghost_stmts, |ghost_stmt_cpn, ghost_stmt| {
                Self::encode_annotation(tcx, &ghost_stmt, ghost_stmt_cpn);
            });
            body_cpn.fill_ghost_decl_blocks(
                &ghost_decl_blocks,
                |mut ghost_decl_block_cpn, ghost_decl_block| {
                    Self::encode_annotation(
                        tcx,
                        &ghost_decl_block,
                        ghost_decl_block_cpn.reborrow().init_start(),
                    );
                    Self::encode_span_data(
                        tcx,
                        &ghost_decl_block.block_end_span().data(),
                        ghost_decl_block_cpn.init_close_brace_span(),
                    );
                },
            );

            Self::encode_visibility(tcx.visibility(def_id), body_cpn.reborrow().init_visibility());
        }

        fn encode_unsafety(us: hir::Safety, mut us_cpn: unsafety_cpn::Builder<'_>) {
            match us {
                hir::Safety::Safe => us_cpn.set_safe(()),
                hir::Safety::Unsafe => us_cpn.set_unsafe(()),
            }
        }

        fn encode_hir_generics(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            hir_gens: &hir::Generics,
            mut hir_gens_cpn: hir_generics_cpn::Builder<'_>,
        ) {
            debug!("Encoding HIR generics {:?}", hir_gens);
            hir_gens_cpn.fill_params(hir_gens.params, |param_cpn, param| {
                Self::encode_hir_generic_param(enc_ctx, param, param_cpn);
            });
            let span_cpn = hir_gens_cpn.init_span();
            Self::encode_span_data(enc_ctx.tcx, &hir_gens.span.data(), span_cpn);
        }

        fn encode_hir_generic_param(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            p: &hir::GenericParam,
            mut p_cpn: hir_generic_param_cpn::Builder<'_>,
        ) {
            let name_cpn = p_cpn.reborrow().init_name();
            Self::encode_hir_generic_param_name(enc_ctx, p.def_id, &p.name, name_cpn);
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
            def_id: rustc_span::def_id::LocalDefId,
            n: &hir::ParamName,
            n_cpn: hir_generic_param_name_cpn::Builder<'_>,
        ) {
            match n {
                hir::ParamName::Plain(ident) => {
                    let ident_cpn = n_cpn.init_plain();
                    Self::encode_ident(enc_ctx, ident, ident_cpn);
                }
                hir::ParamName::Fresh => {
                    let id_cpn = n_cpn.init_fresh();
                    capnp_utils::encode_u_int128(
                        def_id.local_def_index.as_usize().try_into().unwrap(),
                        id_cpn,
                    );
                }
                hir::ParamName::Error(_) => bug!(),
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
                    Self::encode_const_operand(tcx, enc_ctx, constant, constant_cpn);
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
            //debug!("Encoding SpanData {:?}", span_data);
            if span_data.is_dummy() {
                span_data_cpn.set_dummy(());
                return;
            }
            let mut span_data_regular_cpn = span_data_cpn.init_regular();
            let sm = tcx.sess.source_map();
            let lo_cpn = span_data_regular_cpn.reborrow().init_lo();
            let lo = sm.lookup_char_pos(span_data.lo);
            Self::encode_loc(&lo, lo_cpn);
            let hi_cpn = span_data_regular_cpn.init_hi();
            let hi = sm.lookup_char_pos(span_data.hi);
            Self::encode_loc(&hi, hi_cpn);
        }

        fn encode_loc(loc: &rustc_span::Loc, mut loc_cpn: loc_cpn::Builder<'_>) {
            //debug!("Encoding Loc {:?}", loc);
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
            //debug!("Encoding SourceFile {:?}", src_file);
            let name_cpn = src_file_cpn.init_name();
            Self::encode_file_name(&src_file.name, name_cpn);
        }

        fn encode_file_name(fname: &rustc_span::FileName, fname_cpn: file_name_cpn::Builder<'_>) {
            //debug!("Encoding FileName {:?}", fname);
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
            //debug!("Encoding RealFileName {:?}", real_fname);
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
            contract_annots: LinkedList<Box<GhostRange>>,
            body_contract_span: &rustc_span::SpanData,
            mut contract_cpn: contract_cpn::Builder<'_>,
        ) {
            let span_cpn = contract_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, body_contract_span, span_cpn);
            contract_cpn.fill_annotations(&contract_annots, |annot_cpn, annot| {
                Self::encode_annotation(tcx, &annot, annot_cpn);
            });
        }

        fn encode_annotation(
            tcx: TyCtxt<'tcx>,
            annot: &GhostRange,
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

        fn compute_local_decl_effective_mutability(enc_ctx: &mut EncCtx<'tcx, 'a>, local_decl: &mir::LocalDecl<'tcx>) -> mir::Mutability {
            if local_decl.mutability == mir::Mutability::Mut {
                return local_decl.mutability;
            }
            let local_span_start = local_decl.source_info.span.data().lo;
            let mut_annot_end = local_span_start - rustc_span::BytePos(1);
            let has_mut_annot = enc_ctx.mut_annots.contains(&mut_annot_end);
            if has_mut_annot {
                trace!("Found mut annotation for {:?} at {:?}", local_decl, mut_annot_end);
                return mir::Mutability::Mut;
            } else {
                trace!("No mut annotation found for {:?} at {:?}", local_decl, mut_annot_end);
            }
            local_decl.mutability
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
            Self::encode_mutability(Self::compute_local_decl_effective_mutability(enc_ctx, local_decl), mutability_cpn);

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
                ty::TyKind::Float(_) => ty_kind_cpn.set_float(()),
                ty::TyKind::Char => ty_kind_cpn.set_char(()),
                ty::TyKind::Adt(adt_def, substs) => {
                    let adt_ty_cpn = ty_kind_cpn.init_adt();
                    Self::encode_ty_adt(tcx, enc_ctx, *adt_def, substs, adt_ty_cpn);
                }
                ty::TyKind::Foreign(_) => ty_kind_cpn.set_foreign(()),
                ty::TyKind::RawPtr(ty, mutability) => {
                    let raw_ptr_ty_cpn = ty_kind_cpn.init_raw_ptr();
                    Self::encode_ty_raw_ptr(tcx, enc_ctx, *ty, *mutability, raw_ptr_ty_cpn);
                }
                ty::TyKind::Ref(region, ty, mutability) => {
                    let ref_ty_cpn = ty_kind_cpn.init_ref();
                    Self::encode_ty_ref(tcx, enc_ctx, *region, *ty, *mutability, ref_ty_cpn);
                }
                ty::TyKind::FnDef(def_id, substs) => {
                    let fn_def_ty_cpn = ty_kind_cpn.init_fn_def();
                    Self::encode_ty_fn_def(tcx, enc_ctx, def_id, substs, fn_def_ty_cpn);
                }
                ty::TyKind::FnPtr(binder, header) => {
                    let fn_ptr_ty_cpn = ty_kind_cpn.init_fn_ptr();
                    let fn_sig = binder
                        .skip_binder();
                    let output_cpn = fn_ptr_ty_cpn.init_output();
                    Self::encode_ty(tcx, enc_ctx, fn_sig.output(), output_cpn);
                }
                ty::TyKind::Dynamic(_, _, _) => ty_kind_cpn.set_dynamic(()),
                ty::TyKind::Closure(def_id, gen_args) => {
                    let mut closure_ty_cpn = ty_kind_cpn.init_closure();
                    closure_ty_cpn.set_def_id(&tcx.def_path_str(*def_id));
                    closure_ty_cpn.fill_substs(gen_args.iter(), |gen_arg_cpn, gen_arg| {
                        Self::encode_gen_arg(tcx, enc_ctx, gen_arg, gen_arg_cpn);
                    });
                }
                ty::TyKind::CoroutineClosure(_, _) => ty_kind_cpn.set_coroutine_closure(()),
                ty::TyKind::Coroutine(_, _) => ty_kind_cpn.set_coroutine(()),
                ty::TyKind::CoroutineWitness(_, _) => ty_kind_cpn.set_coroutine_witness(()),
                ty::TyKind::Never => ty_kind_cpn.set_never(()),
                ty::TyKind::Tuple(gen_args) => {
                    ty_kind_cpn.fill_tuple(gen_args.iter(), |gen_arg_cpn, gen_arg| {
                        Self::encode_ty(tcx, enc_ctx, gen_arg, gen_arg_cpn);
                    });
                }
                ty::TyKind::Alias(kind, alias_ty) => {
                    let mut alias_ty_cpn = ty_kind_cpn.init_alias();
                    alias_ty_cpn.set_kind(match kind {
                        ty::AliasTyKind::Projection => crate::vf_mir_capnp::AliasTyKind::Projection,
                        ty::AliasTyKind::Inherent => crate::vf_mir_capnp::AliasTyKind::Inherent,
                        ty::AliasTyKind::Opaque => crate::vf_mir_capnp::AliasTyKind::Opaque,
                        ty::AliasTyKind::Weak => crate::vf_mir_capnp::AliasTyKind::Weak,
                    });
                    alias_ty_cpn.set_def_id(&tcx.def_path_str(alias_ty.def_id));
                    alias_ty_cpn.fill_args(alias_ty.args, |arg_cpn, arg| {
                        Self::encode_gen_arg(tcx, enc_ctx, arg, arg_cpn);
                    });
                }
                ty::TyKind::Param(param_ty) => {
                    ty_kind_cpn.set_param(&param_ty.to_string());
                }
                ty::TyKind::Bound(_, _) => ty_kind_cpn.set_bound(()),
                ty::TyKind::Placeholder(_) => ty_kind_cpn.set_placeholder(()),
                ty::TyKind::Infer(_) => ty_kind_cpn.set_infer(()),
                ty::TyKind::Error(_) => ty_kind_cpn.set_error(()),
                ty::TyKind::Str => ty_kind_cpn.set_str(()),
                ty::TyKind::Array(ty, size) => {
                    let mut array_ty_cpn = ty_kind_cpn.init_array();
                    Self::encode_ty(tcx, enc_ctx, *ty, array_ty_cpn.reborrow().init_elem_ty());
                    Self::encode_typesystem_constant(tcx, enc_ctx, size, array_ty_cpn.init_size());
                }
                ty::TyKind::Pat(_, _) => ty_kind_cpn.set_pattern(()),
                ty::TyKind::Slice(elem_ty) => {
                    let elem_ty_cpn = ty_kind_cpn.init_slice();
                    Self::encode_ty(tcx, enc_ctx, *elem_ty, elem_ty_cpn);
                }
                ty::TyKind::UnsafeBinder(_) => todo!()
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
            adt_def: ty::AdtDef<'tcx>,
            substs: &'tcx &'tcx ty::List<ty::GenericArg<'tcx>>,
            mut adt_ty_cpn: adt_ty_cpn::Builder<'_>,
        ) {
            debug!("Encoding algebraic data type {:?}", adt_def);
            let adt_did_cpn = adt_ty_cpn.reborrow().init_id();
            Self::encode_adt_def_id(enc_ctx, adt_def.did(), adt_did_cpn);

            let substs_cpn = adt_ty_cpn.reborrow().init_substs(substs.len());
            Self::encode_ty_args(enc_ctx, substs, substs_cpn);

            let kind_cpn = adt_ty_cpn.init_kind();
            Self::encode_adt_kind(adt_def.adt_kind(), kind_cpn);
            // Definitions we use should be encoded later
            enc_ctx.add_req_adt(adt_def);
        }

        fn encode_ty_raw_ptr(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ty: ty::Ty<'tcx>,
            mutability: mir::Mutability,
            mut raw_ptr_ty_cpn: raw_ptr_ty_cpn::Builder<'_>,
        ) {
            let ty_cpn = raw_ptr_ty_cpn.reborrow().init_ty();
            Self::encode_ty(tcx, enc_ctx, ty, ty_cpn);
            let mut_cpn = raw_ptr_ty_cpn.init_mutability();
            Self::encode_mutability(mutability, mut_cpn);
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
            substs: &'tcx &'tcx ty::List<ty::GenericArg<'tcx>>,
            mut fn_def_ty_cpn: fn_def_ty_cpn::Builder<'_>,
        ) {
            let def_path = tcx.def_path_str(*def_id);
            let late_bound_generic_param_count =
                tcx.fn_sig(def_id).skip_binder().bound_vars().len();
            debug!(
                "Encoding FnDef for {} with {} late-bound generic params and substs {:?}",
                def_path, late_bound_generic_param_count, substs
            );
            fn_def_ty_cpn.set_late_bound_generic_param_count(
                late_bound_generic_param_count.try_into().unwrap(),
            );
            let mut id_cpn = fn_def_ty_cpn.reborrow().init_id();
            id_cpn.set_name(&def_path);

            let substs_cpn = fn_def_ty_cpn.init_substs(substs.len());
            Self::encode_ty_args(enc_ctx, substs, substs_cpn);
        }

        fn encode_region(region: ty::Region<'tcx>, mut region_cpn: region_cpn::Builder<'_>) {
            debug!("Encoding region {:?}", region);
            match region.kind() {
                ty::RegionKind::ReEarlyParam(early_bound_region) => {
                    if early_bound_region.name.as_str() == "'_" {
                        let id = Self::anonymous_early_bound_lifetime_name(early_bound_region.index);
                        region_cpn.set_id(&id);
                    } else {
                        region_cpn.set_id(early_bound_region.name.as_str());
                    }
                }
                ty::RegionKind::ReBound(de_bruijn_index, bound_region) => match bound_region.kind {
                    ty::BoundRegionKind::Anon => todo!(),
                    ty::BoundRegionKind::Named(def_id, symbol) => {
                        if symbol.as_str() == "'_" {
                            let id = Self::anonymous_late_bound_lifetime_name(def_id.index.as_usize());
                            region_cpn.set_id(&id);
                        } else {
                            region_cpn.set_id(symbol.as_str());
                        }
                    }
                    ty::BoundRegionKind::ClosureEnv => todo!(),
                },
                ty::RegionKind::ReLateParam(_debruijn_index) => bug!(),
                ty::RegionKind::ReStatic => region_cpn.set_id("'static"),
                ty::RegionKind::ReVar(_) | ty::RegionKind::ReErased => {
                    // Todo @Nima: We should find a mapping of `RegionVid`s and lifetime variable names at `hir`
                    region_cpn.set_id(/*&format!("{:?}", region)*/ "'<erased>");
                }
                ty::RegionKind::RePlaceholder(_placeholder_region) => bug!(),
                _ => bug!(),
            }
        }

        fn encode_gen_arg(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            gen_arg: ty::GenericArg<'tcx>,
            gen_arg_cpn: gen_arg_cpn::Builder<'_>,
        ) {
            debug!("Encoding generic arg {:?}", gen_arg);
            let kind_cpn = gen_arg_cpn.init_kind();
            let kind = gen_arg.unpack();
            match kind {
                ty::GenericArgKind::Lifetime(region) => {
                    let region_cpn = kind_cpn.init_lifetime();
                    Self::encode_region(region, region_cpn);
                }
                ty::GenericArgKind::Type(ty) => {
                    let ty_cpn = kind_cpn.init_type();
                    Self::encode_ty(tcx, enc_ctx, ty, ty_cpn);
                }
                ty::GenericArgKind::Const(ty_const) => {
                    Self::encode_typesystem_constant(tcx, enc_ctx, &ty_const, kind_cpn.init_const());
                }
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

            basic_block_cpn.fill_statements(
                &basic_block_data.statements,
                |statement_cpn, statement| {
                    Self::encode_statement(tcx, enc_ctx, statement, statement_cpn);
                },
            );

            let terminator_cpn = basic_block_cpn.reborrow().init_terminator();
            Self::encode_terminator(tcx, enc_ctx, basic_block_data.terminator(), terminator_cpn);

            basic_block_cpn.set_is_cleanup(basic_block_data.is_cleanup);
        }

        #[inline]
        fn encode_basic_block_id(
            basic_block_idx: mir::BasicBlock,
            mut basic_block_id_cpn: basic_block_id_cpn::Builder<'_>,
        ) {
            basic_block_id_cpn.set_index(basic_block_idx.as_u32());
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
            Self::encode_statement_kind(tcx, enc_ctx, statement.source_info.span, &statement.kind, kind_cpn);
        }

        fn encode_source_info(
            tcx: TyCtxt<'tcx>,
            src_info: &mir::SourceInfo,
            mut src_info_cpn: source_info_cpn::Builder<'_>,
        ) {
            //debug!("Encoding SourceInfo {:?}", src_info);
            let span_cpn = src_info_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, &src_info.span.data(), span_cpn);
        }

        fn encode_statement_kind(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            span: rustc_span::Span,
            statement_kind: &mir::StatementKind<'tcx>,
            mut statement_kind_cpn: statement_kind_cpn::Builder<'_>,
        ) {
            match statement_kind {
                mir::StatementKind::Assign(box (lhs_place, rhs_rval)) => {
                    let mut assign_data_cpn = statement_kind_cpn.init_assign();
                    let lhs_place_cpn = assign_data_cpn.reborrow().init_lhs_place();
                    Self::encode_place(enc_ctx, lhs_place, lhs_place_cpn);
                    let rhs_rvalue_cpn = assign_data_cpn.init_rhs_rvalue();
                    Self::encode_rvalue(tcx, enc_ctx, span, rhs_rval, rhs_rvalue_cpn);
                }
                mir::StatementKind::Nop => statement_kind_cpn.set_nop(()),
                // Todo @Nima: For now we do not support many statements and treat them as Nop
                _ => statement_kind_cpn.set_nop(()),
            }
        }

        fn encode_rvalue(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            span: rustc_span::Span,
            rvalue: &mir::Rvalue<'tcx>,
            mut rvalue_cpn: rvalue_cpn::Builder<'_>,
        ) {
            debug!("Encoding Rvalue {:?}", rvalue);
            match rvalue {
                mir::Rvalue::Use(operand) => {
                    let operand_cpn = rvalue_cpn.init_use();
                    Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                }
                // [x; 32]
                mir::Rvalue::Repeat(operand, ty_const) => rvalue_cpn.set_repeat(()),
                // &x or &mut x
                mir::Rvalue::Ref(region, bor_kind, place) => {
                    let mut ref_data_cpn = rvalue_cpn.init_ref();
                    let place_ty = place.ty(&enc_ctx.body().local_decls, tcx);
                    let place_ty_cpn = ref_data_cpn.reborrow().init_place_ty();
                    Self::encode_ty(tcx, enc_ctx, place_ty.ty, place_ty_cpn);
                    let region_cpn = ref_data_cpn.reborrow().init_region();
                    Self::encode_region(*region, region_cpn);
                    let bor_kind_cpn = ref_data_cpn.reborrow().init_bor_kind();
                    Self::encode_borrow_kind(bor_kind, bor_kind_cpn);
                    let place_cpn = ref_data_cpn.reborrow().init_place();
                    Self::encode_place(enc_ctx, place, place_cpn);
                    if let Ok(source_text) = enc_ctx.tcx.sess.source_map().span_to_snippet(span) {
                        let is_identifier = source_text.chars().all(|c| c.is_alphanumeric() || c == '_');
                        ref_data_cpn.set_is_implicit(is_identifier);
                    }
                    let typing_env = ty::TypingEnv { typing_mode: ty::TypingMode::PostAnalysis, param_env: ty::ParamEnv::empty() };
                    ref_data_cpn.set_place_does_not_need_drop(!place_ty.ty.needs_drop(tcx, typing_env));
                }
                mir::Rvalue::ThreadLocalRef(def_id) => rvalue_cpn.set_thread_local_ref(()),
                mir::Rvalue::RawPtr(raw_ptr_kind, place) => {
                    let mut ao_data_cpn = rvalue_cpn.init_address_of();
                    let mutability_cpn = ao_data_cpn.reborrow().init_mutability();
                    Self::encode_mutability(match raw_ptr_kind {
                        mir::RawPtrKind::Mut => mir::Mutability::Mut,
                        mir::RawPtrKind::Const => mir::Mutability::Not,
                        mir::RawPtrKind::FakeForPtrMetadata => todo!(),
                    }, mutability_cpn);
                    let place_cpn = ao_data_cpn.init_place();
                    Self::encode_place(enc_ctx, place, place_cpn);
                }
                mir::Rvalue::Len(place) => rvalue_cpn.set_len(()),
                mir::Rvalue::Cast(cast_kind, operand, ty) => {
                    let mut cast_data_cpn = rvalue_cpn.init_cast();
                    let operand_cpn = cast_data_cpn.reborrow().init_operand();
                    Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                    let ty_cpn = cast_data_cpn.init_ty();
                    Self::encode_ty(tcx, enc_ctx, *ty, ty_cpn);
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
                mir::Rvalue::NullaryOp(null_op, ty) => rvalue_cpn.set_nullary_op(()),
                mir::Rvalue::UnaryOp(un_op, operand) => {
                    let mut un_op_data_cpn = rvalue_cpn.init_unary_op();
                    let un_op_cpn = un_op_data_cpn.reborrow().init_operator();
                    Self::encode_un_op(*un_op, un_op_cpn);
                    let operand_cpn = un_op_data_cpn.reborrow().init_operand();
                    Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                }
                // Read the discriminant of an ADT.
                mir::Rvalue::Discriminant(place) => {
                    if let EncKind::Body(body) = enc_ctx.mode {
                        let ty = place.ty(body, tcx);
                        if let Some(adt_def) = ty.ty.ty_adt_def() {
                            let variants_count = adt_def.variants().len();
                            for i in 0..variants_count {
                                match ty.ty.discriminant_for_variant(tcx, i.into()) {
                                    None => {}
                                    Some(discr) => {
                                        if discr.val != i.try_into().unwrap() {
                                            todo!()
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Self::encode_place(enc_ctx, place, rvalue_cpn.init_discriminant());
                }
                // Creates an aggregate value, like a tuple or struct.
                mir::Rvalue::Aggregate(box aggregate_kind, operands) => {
                    let mut aggregate_data_cpn = rvalue_cpn.init_aggregate();
                    let aggregate_kind_cpn = aggregate_data_cpn.reborrow().init_aggregate_kind();
                    Self::encode_aggregate_kind(enc_ctx, aggregate_kind, aggregate_kind_cpn);
                    aggregate_data_cpn.fill_operands(operands, |operand_cpn, operand| {
                        Self::encode_operand(tcx, enc_ctx, operand, operand_cpn);
                    });
                }
                // Transmutes a `*mut u8` into shallow-initialized `Box<T>`.
                mir::Rvalue::ShallowInitBox(operand, ty) => rvalue_cpn.set_shallow_init_box(()),
                mir::Rvalue::CopyForDeref(place) => {
                    let operand_cpn = rvalue_cpn.init_use();
                    let place_cpn = operand_cpn.init_copy();
                    Self::encode_place(enc_ctx, place, place_cpn);
                }
                mir::Rvalue::WrapUnsafeBinder(_, _) => todo!(),
            }
        }

        fn encode_ty_args(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            targs: &ty::List<ty::GenericArg<'tcx>>,
            mut targs_cpn: capnp::struct_list::Builder<'_, gen_arg_cpn::Owned>,
        ) {
            for (idx, targ) in targs.iter().enumerate() {
                let targ_cpn = targs_cpn.reborrow().get(idx);
                Self::encode_gen_arg(enc_ctx.tcx, enc_ctx, targ, targ_cpn);
            }
        }

        fn encode_aggregate_kind(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            agg_kind: &mir::AggregateKind<'tcx>,
            mut agg_kind_cpn: aggregate_kind_cpn::Builder<'_>,
        ) {
            match agg_kind {
                mir::AggregateKind::Array(_ty) => {
                    Self::encode_ty(enc_ctx.tcx, enc_ctx, *_ty, agg_kind_cpn.init_array());
                }
                mir::AggregateKind::Tuple => agg_kind_cpn.set_tuple(()),
                mir::AggregateKind::Adt(
                    def_id,
                    variant_idx,
                    gen_args,
                    _user_type_annot_idx_opt,
                    union_active_field_opt,
                ) => {
                    let mut adt_data_cpn = agg_kind_cpn.init_adt();
                    let adt_id_cpn = adt_data_cpn.reborrow().init_adt_id();
                    Self::encode_adt_def_id(enc_ctx, *def_id, adt_id_cpn);

                    adt_data_cpn.set_variant_idx(variant_idx.as_u32());
                    adt_data_cpn.set_union_active_field(match union_active_field_opt {
                        None => 0,
                        Some(idx) => idx.as_u32()
                    });

                    let adt_def = enc_ctx.tcx.adt_def(def_id);
                    let variant = adt_def.variant(*variant_idx);
                    adt_data_cpn.set_variant_id(variant.name.as_str());
                    Self::encode_adt_kind(
                        adt_def.adt_kind(),
                        adt_data_cpn.reborrow().init_adt_kind(),
                    );
                    adt_data_cpn
                        .reborrow()
                        .fill_fields(&variant.fields, |mut f_cpn, f| {
                            f_cpn.set_name(f.name.as_str());
                            let ty = enc_ctx.tcx.type_of(f.did).instantiate_identity();
                            f_cpn.set_is_zero_size(ty.is_phantom_data());
                        });

                    let gen_args_cpn = adt_data_cpn.reborrow().init_gen_args(gen_args.len());
                    Self::encode_ty_args(enc_ctx, gen_args, gen_args_cpn);
                }
                mir::AggregateKind::Closure(def_id, gen_args) => {
                    let mut closure_data_cpn = agg_kind_cpn.init_closure();
                    closure_data_cpn.set_closure_id(&enc_ctx.tcx.def_path_str(*def_id));
                    closure_data_cpn.fill_gen_args(gen_args.iter(), |gen_arg_cpn, gen_arg| {
                        Self::encode_gen_arg(enc_ctx.tcx, enc_ctx, gen_arg, gen_arg_cpn);
                    });
                }
                mir::AggregateKind::Coroutine(_def_id, _substs) => agg_kind_cpn.set_coroutine(()),
                mir::AggregateKind::CoroutineClosure(_def_id, _substs) => agg_kind_cpn.set_coroutine_closure(()),
                mir::AggregateKind::RawPtr(_ty, _mutability) => agg_kind_cpn.set_raw_ptr(()),
            }
        }

        fn encode_borrow_kind(bk: &mir::BorrowKind, mut bk_cpn: borrow_kind_cpn::Builder<'_>) {
            match bk {
                mir::BorrowKind::Shared => bk_cpn.set_shared(()),
                mir::BorrowKind::Mut { kind } => bk_cpn.set_mut(()),
                _ => todo!(),
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
                _ => todo!(),
            }
        }

        fn encode_un_op(un_op: mir::UnOp, mut un_op_cpn: un_op_cpn::Builder<'_>) {
            match un_op {
                mir::UnOp::Not => un_op_cpn.set_not(()),
                mir::UnOp::Neg => un_op_cpn.set_neg(()),
                mir::UnOp::PtrMetadata => todo!(),
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
                mir::TerminatorKind::SwitchInt { discr, targets } => {
                    let switch_int_data_cpn = terminator_kind_cpn.init_switch_int();
                    let switch_ty = discr.ty(enc_ctx.body(), tcx);
                    Self::encode_switch_int_data(
                        tcx,
                        enc_ctx,
                        discr,
                        switch_ty,
                        targets,
                        switch_int_data_cpn,
                    );
                }
                mir::TerminatorKind::UnwindResume => terminator_kind_cpn.set_unwind_resume(()),
                mir::TerminatorKind::UnwindTerminate(_) => terminator_kind_cpn.set_unwind_terminate(()),
                mir::TerminatorKind::Return => terminator_kind_cpn.set_return(()),
                mir::TerminatorKind::Unreachable => terminator_kind_cpn.set_unreachable(()),
                mir::TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    unwind,
                    call_source,
                    fn_span,
                } => {
                    let fn_call_data_cpn = terminator_kind_cpn.init_call();
                    Self::encode_fn_call_data(
                        tcx,
                        enc_ctx,
                        func,
                        args,
                        destination,
                        target,
                        unwind,
                        fn_span,
                        fn_call_data_cpn,
                    );
                }
                mir::TerminatorKind::Drop {
                    place,
                    target,
                    unwind,
                    replace,
                } => {
                    let mut drop_data_cpn = terminator_kind_cpn.init_drop();
                    Self::encode_place(enc_ctx, place, drop_data_cpn.reborrow().init_place());
                    Self::encode_basic_block_id(*target, drop_data_cpn.reborrow().init_target());
                    Self::encode_unwind_action(unwind, drop_data_cpn.reborrow().init_unwind_action());
                }
                mir::TerminatorKind::TailCall { .. } => terminator_kind_cpn.set_tail_call(()),
                mir::TerminatorKind::Assert { .. } => terminator_kind_cpn.set_assert(()),
                mir::TerminatorKind::Yield { .. } => terminator_kind_cpn.set_yield(()),
                mir::TerminatorKind::CoroutineDrop { .. } => terminator_kind_cpn.set_coroutine_drop(()),
                mir::TerminatorKind::FalseEdge { .. } => terminator_kind_cpn.set_false_edge(()),
                mir::TerminatorKind::InlineAsm { .. } => terminator_kind_cpn.set_inline_asm(()),
            }
        }

        fn encode_switch_int_data(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            discr: &mir::Operand<'tcx>,
            discr_ty: ty::Ty<'tcx>,
            targets: &mir::SwitchTargets,
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
            targets: &mir::SwitchTargets,
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
            let mut branches_cpn = targets_cpn.reborrow().init_branches(len);
            for (idx, (val, target)) in targets.iter().enumerate() {
                let mut branch_cpn = branches_cpn.reborrow().get(idx);
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

        fn encode_unwind_action(
            unwind: &UnwindAction,
            mut unwind_action_cpn: unwind_action_cpn::Builder<'_>,
        ) {
            match unwind {
                UnwindAction::Continue => unwind_action_cpn.set_continue(()),
                UnwindAction::Unreachable => unwind_action_cpn.set_unreachable(()),
                UnwindAction::Terminate(_) => unwind_action_cpn.set_terminate(()),
                UnwindAction::Cleanup(basic_block) => {
                    let cleanup_cpn = unwind_action_cpn.init_cleanup();
                    Self::encode_basic_block_id(*basic_block, cleanup_cpn);
                }
            }
        }

        fn encode_fn_call_data(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            func: &mir::Operand<'tcx>,
            args: &Box<[Spanned<mir::Operand<'tcx>>]>,
            destination: &mir::Place<'tcx>,
            target: &Option<mir::BasicBlock>,
            unwind: &UnwindAction,
            fn_span: &rustc_span::Span,
            mut fn_call_data_cpn: fn_call_data_cpn::Builder<'_>,
        ) {
            let func_cpn = fn_call_data_cpn.reborrow().init_func();
            let func_span_opt = Self::encode_operand(tcx, enc_ctx, func, func_cpn);

            // Encoding args
            fn_call_data_cpn.fill_args(args, |arg_cpn, arg| {
                Self::encode_operand(tcx, enc_ctx, &arg.node, arg_cpn);
            });

            // Encode destination
            let mut destination_cpn = fn_call_data_cpn.reborrow().init_destination();
            match target {
                Option::None => destination_cpn.set_nothing(()), // diverging call
                Option::Some(dest_bblock_id) => {
                    let mut destination_data_cpn = destination_cpn.init_something();
                    let place_cpn = destination_data_cpn.reborrow().init_place();
                    Self::encode_place(enc_ctx, destination, place_cpn);
                    let basic_block_id_cpn = destination_data_cpn.init_basic_block_id();
                    Self::encode_basic_block_id(*dest_bblock_id, basic_block_id_cpn);
                }
            }

            Self::encode_unwind_action(unwind, fn_call_data_cpn.reborrow().init_unwind_action());

            let call_span_data_cpn = fn_call_data_cpn.reborrow().init_call_span();
            Self::encode_span_data(tcx, &fn_span.data(), call_span_data_cpn);

            if let Some(func_span) = func_span_opt {
                let func_span_hi = func_span.hi();
                let ghost_generic_arg_lists: Vec<_> = enc_ctx
                    .annots
                    .extract_if(|annot| {
                        annot.kind == GhostRangeKind::GenericArgs
                            && annot.span().unwrap().lo() == func_span_hi
                    })
                    .collect();
                assert!(ghost_generic_arg_lists.len() <= 1);
                if ghost_generic_arg_lists.len() == 1 {
                    let annot_opt_cpn = fn_call_data_cpn.reborrow().init_ghost_generic_arg_list();
                    let annot_cpn = annot_opt_cpn.init_something();
                    Self::encode_annotation(tcx, &ghost_generic_arg_lists[0], annot_cpn);
                }
            }
        }

        fn encode_operand(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            operand: &mir::Operand<'tcx>,
            operand_cpn: operand_cpn::Builder<'_>,
        ) -> Option<Span> {
            debug!("Encoding Operand {:?}", operand);
            match operand {
                mir::Operand::Copy(place) => {
                    let place_cpn = operand_cpn.init_copy();
                    Self::encode_place(enc_ctx, place, place_cpn);
                    None
                }
                mir::Operand::Move(place) => {
                    let place_cpn = operand_cpn.init_move();
                    Self::encode_place(enc_ctx, place, place_cpn);
                    None
                }
                mir::Operand::Constant(box constant) => {
                    let constant_cpn = operand_cpn.init_constant();
                    Some(Self::encode_const_operand(tcx, enc_ctx, constant, constant_cpn))
                }
            }
        }

        fn encode_const_operand(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            const_operand: &mir::ConstOperand<'tcx>,
            mut const_operand_cpn: const_operand_cpn::Builder<'_>,
        ) -> Span {
            let span_data_cpn = const_operand_cpn.reborrow().init_span();
            Self::encode_span_data(tcx, &const_operand.span.data(), span_data_cpn);
            let const_cpn = const_operand_cpn.init_const();
            Self::encode_const(tcx, enc_ctx, &const_operand.const_, const_cpn);
            const_operand.span
        }

        fn encode_const(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            const_: &mir::Const<'tcx>,
            const_cpn: const_cpn::Builder<'_>,
        ) {
            match const_ {
                mir::Const::Ty(ty, ty_const) => {
                    let mut ty_const_cpn = const_cpn.init_ty();
                    Self::encode_ty(tcx, enc_ctx, *ty, ty_const_cpn.reborrow().init_ty());
                    Self::encode_typesystem_constant(tcx, enc_ctx, ty_const, ty_const_cpn.init_const());
                }
                mir::Const::Val(const_value, ty) => {
                    let mut val_cpn = const_cpn.init_val();
                    Self::encode_const_value(
                        tcx,
                        *ty,
                        const_value,
                        val_cpn.reborrow().init_const_value(),
                    );
                    Self::encode_ty(tcx, enc_ctx, *ty, val_cpn.init_ty());
                }
                mir::Const::Unevaluated(unevaluated_const, ty) => {
                    if let Ok(const_value) = const_.eval(tcx, enc_ctx.body().typing_env(tcx), Span::default()) {
                        let mut val_cpn = const_cpn.init_val();
                        Self::encode_const_value(
                            tcx,
                            *ty,
                            &const_value,
                            val_cpn.reborrow().init_const_value(),
                        );
                        Self::encode_ty(tcx, enc_ctx, *ty, val_cpn.init_ty());
                    } else {
                        let mut unevaluated_cpn = const_cpn.init_unevaluated();
                        unevaluated_cpn.set_def(tcx.def_path_str(unevaluated_const.def).as_str());
                        unevaluated_cpn.fill_args(unevaluated_const.args, |arg_cpn, arg| {
                            Self::encode_gen_arg(tcx, enc_ctx, arg, arg_cpn);
                        });
                    }
                }
            }
        }

        fn encode_typesystem_constant(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ty_const: &ty::Const<'tcx>,
            ty_const_cpn: ty_const_cpn::Builder<'_>,
        ) {
            debug!("Encoding typesystem constant {:?}", ty_const);
            let mut ty_const = *ty_const;
            if let ty::ConstKind::Unevaluated(_) = ty_const.kind() {
                let typing_env = ty::TypingEnv { typing_mode: ty::TypingMode::PostAnalysis, param_env: ty::ParamEnv::empty() };
                if let Ok(ty_const_normalized) = tcx.try_normalize_erasing_regions(typing_env, ty_const) {
                    ty_const = ty_const_normalized;
                }
            }
            let kind_cpn = ty_const_cpn.init_kind();
            Self::encode_const_kind(tcx, enc_ctx, &ty_const.kind(), kind_cpn);
        }

        fn encode_const_kind(
            tcx: TyCtxt<'tcx>,
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            const_kind: &ty::ConstKind<'tcx>,
            mut const_kind_cpn: const_kind_cpn::Builder<'_>,
        ) {
            use ty::ConstKind as CK;
            match const_kind {
                // A const generic parameter.
                CK::Param(param_const) => {
                    let mut param_const_cpn = const_kind_cpn.init_param();
                    param_const_cpn.set_index(param_const.index);
                    param_const_cpn.set_name(param_const.name.as_str());
                }
                // Infer the value of the const.
                CK::Infer(infer_const) => const_kind_cpn.set_infer(()),
                // Bound const variable, used only when preparing a trait query.
                CK::Bound(debruijn_idx, bound_var) => const_kind_cpn.set_bound(()),
                // A placeholder const - universally quantified higher-ranked const.
                CK::Placeholder(placeholder_const) => const_kind_cpn.set_placeholder(()),
                // Used in the HIR by using `Unevaluated` everywhere and later normalizing to one of the other
                // variants when the code is monomorphic enough for that.
                CK::Unevaluated(unevaluated) => const_kind_cpn.set_unevaluated(()),
                // Used to hold computed value.
                CK::Value(value) => {
                    let mut value_cpn = const_kind_cpn.init_value();
                    Self::encode_ty(tcx, enc_ctx, value.ty, value_cpn.reborrow().init_ty());
                    Self::encode_val_tree(tcx, &value.valtree, value_cpn.init_val_tree());
                }
                // A placeholder for a const which could not be computed; this is
                // propagated to avoid useless error messages.
                CK::Error(delay_span_bug_emitted) => const_kind_cpn.set_error(()),
                CK::Expr(_) => const_kind_cpn.set_expr(()),
            }
        }

        fn encode_val_tree(
            tcx: TyCtxt<'tcx>,
            val_tree: &ty::ValTree<'tcx>,
            val_tree_cpn: val_tree_cpn::Builder<'_>,
        ) {
            use ty::ValTreeKind as VT;
            match **val_tree {
                // Used only for types with `layout::abi::Scalar` ABI and ZSTs.
                VT::Leaf(scalar_int) => {
                    let scalar_int_cpn = val_tree_cpn.init_leaf();
                    Self::encode_scalar_int(tcx, scalar_int, scalar_int_cpn);
                }
                // Used only for `&[u8]` and `&str`
                VT::Branch(_) => todo!(),
            }
        }

        fn encode_const_value(
            tcx: TyCtxt<'tcx>,
            ty: ty::Ty<'tcx>,
            const_value: &mir::ConstValue<'tcx>,
            mut const_value_cpn: const_value_cpn::Builder<'_>,
        ) {
            use mir::ConstValue as CV;
            match const_value {
                // Used only for types with `layout::abi::Scalar` ABI and ZSTs.
                CV::Scalar(rustc_middle::mir::interpret::Scalar::Int(scalar_int)) => {
                    // `Scalar`s are a limited number of primitives.
                    // It is easier to encode the value itself instead of its internal representation in the compiler
                    let scalar_cpn = const_value_cpn.init_scalar();
                    let scalar_int_cpn = scalar_cpn.init_int();
                    Self::encode_scalar_int(tcx, scalar_int, scalar_int_cpn);
                }
                CV::Scalar(rustc_middle::mir::interpret::Scalar::Ptr(_, _)) => {
                    let mut scalar_con = const_value_cpn.init_scalar();
                    scalar_con.set_ptr(());
                }
                CV::ZeroSized => {
                    trace!("mir::ConstValue::ZeroSized for type {:?}", ty);
                    const_value_cpn.set_zero_sized(());
                }
                // Used only for `&[u8]` and `&str`
                CV::Slice { data, meta } => {
                    let allocation = data.inner();
                    let bytes = allocation.get_bytes_unchecked(AllocRange {
                        start: rustc_abi::Size::ZERO,
                        size: allocation.size(),
                    });
                    const_value_cpn.set_slice(bytes);
                }
                CV::Indirect { alloc_id, offset } => todo!(),
            }
        }

        fn encode_scalar_int(
            tcx: TyCtxt<'tcx>,
            scalar_int: &rustc_middle::ty::ScalarInt,
            mut scalar_int_cpn: scalar_int_cpn::Builder<'_>,
        ) {
            capnp_utils::encode_u_int128(scalar_int.to_bits_unchecked(), scalar_int_cpn.reborrow().init_data());
            scalar_int_cpn.set_size(scalar_int.size().bytes().try_into().unwrap());
        }

        fn encode_place(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            place: &mir::Place<'tcx>,
            mut place_cpn: place_cpn::Builder<'_>,
        ) {
            let local_decl_id_cpn = place_cpn.reborrow().init_local();
            Self::encode_local_decl_id(place.local, local_decl_id_cpn);
            let decl = &enc_ctx.body().local_decls()[place.local];
            place_cpn.set_local_is_mutable(Self::compute_local_decl_effective_mutability(enc_ctx, decl) == mir::Mutability::Mut);

            let local = &enc_ctx.body().local_decls()[place.local];
            let mut pty = mir::PlaceTy::from_ty(local.ty);
            let mut kind = PlaceKind::Other;
            if place.projection.len() == 2 && local.ty.is_box() {
                // The only projection that can be applied to a Box is (X.0: std::ptr::Unique<T>).0: std::ptr::NonNull<T>
                let place_projection_cpn = place_cpn.reborrow().init_projection(1);
                let place_elem_cpn = place_projection_cpn.get(0);
                let ty_cpn = place_elem_cpn.init_box_as_non_null();
                Self::encode_ty(enc_ctx.tcx, enc_ctx, local.ty.boxed_ty().unwrap(), ty_cpn);
            } else {
                place_cpn.reborrow().fill_projection(place.projection, |place_elm_cpn, place_elm| {
                    kind = Self::encode_place_element(enc_ctx, pty.ty, &place_elm, place_elm_cpn, kind);
                    pty = pty.projection_ty(enc_ctx.tcx, place_elm);
                });
            }
            let mut kind_cpn = place_cpn.init_kind();
            match kind {
                PlaceKind::MutableRef => kind_cpn.set_mutable_ref(()),
                PlaceKind::SharedRef => kind_cpn.set_shared_ref(()),
                PlaceKind::Other => kind_cpn.set_other(()),
            }
        }

        fn encode_place_element(
            enc_ctx: &mut EncCtx<'tcx, 'a>,
            ty: ty::Ty<'tcx>,
            place_elm: &mir::PlaceElem<'tcx>,
            mut place_elm_cpn: place_element_cpn::Builder<'_>,
            place_kind: PlaceKind
        ) -> PlaceKind {
            debug!(
                "Encoding place element {:?} Projecting from {:?}",
                place_elm, ty
            );
            match place_elm {
                mir::ProjectionElem::Deref => {
                    place_elm_cpn.set_deref(());
                    match ty.kind() {
                        ty::TyKind::Ref(_, _, mutability) =>
                            match mutability {
                                ty::Mutability::Not => PlaceKind::SharedRef,
                                ty::Mutability::Mut => PlaceKind::MutableRef,
                            },
                        _ => PlaceKind::Other,
                    }
                }
                mir::ProjectionElem::Field(field, fty) => {
                    let mut field_data_cpn = place_elm_cpn.init_field();
                    field_data_cpn.set_index(field.as_u32());
                    match ty.kind() {
                        ty::TyKind::Adt(adt_def, gen_args) => {
                            if adt_def.is_struct() {
                                let name = adt_def.non_enum_variant().fields[*field].name;
                                let name_cpn = field_data_cpn.reborrow().init_name();
                                Self::encode_symbol(&name, name_cpn.init_something());
                            }
                        }
                        _ => {}
                    }
                    let ty_cpn = field_data_cpn.init_ty();
                    Self::encode_ty(enc_ctx.tcx, enc_ctx, *fty, ty_cpn);
                    /* Todo @Nima: When `encode_ty` becomes a method of `EncCtx` there would not be
                     * such strange arguments `enc_ctx.tcx` and `enc_tcx`
                     */
                    PlaceKind::Other
                }
                mir::ProjectionElem::Index(_) => {
                    place_elm_cpn.set_index(());
                    PlaceKind::Other
                }
                mir::ProjectionElem::ConstantIndex{ .. } => {
                    place_elm_cpn.set_constant_index(());
                    PlaceKind::Other
                }
                mir::ProjectionElem::Subslice{ .. } => {
                    place_elm_cpn.set_subslice(());
                    PlaceKind::Other
                }
                mir::ProjectionElem::Downcast(symbol, variant_idx) => {
                    place_elm_cpn.set_downcast(variant_idx.as_u32());
                    PlaceKind::Other
                }
                mir::ProjectionElem::OpaqueCast(_) => {
                    place_elm_cpn.set_opaque_cast(());
                    PlaceKind::Other
                }
                mir::ProjectionElem::Subtype(_) => {
                    place_elm_cpn.set_subtype(());
                    PlaceKind::Other
                }
                mir::ProjectionElem::UnwrapUnsafeBinder(_) => todo!(),
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
    use rustc_middle::mir::pretty::PrettyPrintMirOptions;
    use rustc_middle::ty::TyCtxt;

    pub fn mir_body_pretty_string<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>) -> String {
        use rustc_middle::mir::pretty::write_mir_fn;
        let mut buf: Vec<u8> = Vec::new();
        write_mir_fn(tcx, body, &mut |_, _| Ok(()), &mut buf, PrettyPrintMirOptions { include_extra_comments: false }).expect(&format!(
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
        let body_span = hir_body.value.span;
        // if tcx.is_closure(def_id) {
        //     // If the MIR function is a closure, and if the closure body span
        //     // starts from a macro, but it's content is not in that macro, try
        //     // to find a non-macro callsite, and instrument the spans there
        //     // instead.
        //     loop {
        //         let expn_data = body_span.ctxt().outer_expn_data();
        //         if expn_data.is_root() {
        //             break;
        //         }
        //         if let ExpnKind::Macro { .. } = expn_data.kind {
        //             body_span = expn_data.call_site;
        //         } else {
        //             break;
        //         }
        //     }
        // }
        body_span
    }

    pub fn body_imp_span<'tcx>(tcx: TyCtxt<'tcx>, mir_body: &mir::Body<'tcx>) -> SpanData {
        let def_id = mir_body.source.def_id();
        let hir_body = hir_utils::fn_body(tcx, def_id);
        let body_imp_span = get_hir_body_span(tcx, &hir_body, def_id);
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
        let body_span = get_hir_body_span(tcx, &hir_body, def_id);
        let cspan = fn_sig.span.shrink_to_hi().with_hi(body_span.lo());
        debug!(
            "Contract span for {:?} is {:?}",
            mir_body.source.instance, cspan
        );
        cspan.data()
    }
}

// Todo @Nima: Some mut vars might not need to be mut.
// Todo @Nima: The encoding functions need to be turned to method to prevent passing context around
// Todo @Nima: Change the encode functions that require the EncCtx as a parameter to methods of EncCtx
// Todo @Nima: Extract lifetime beginning and ends to produce and consume their tokens in those compiler-inferred places
