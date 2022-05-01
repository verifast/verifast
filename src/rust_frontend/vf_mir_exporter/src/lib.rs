#![feature(rustc_private)]

/***
 * TODO @Nima:
 * 1- Is it really necessary to register queries? read mir pretty printer.
 * The mir pretty printer uses optimized_mir/promoted_mir which are lower level generated mir
 * 2- Where are the data type definitions
 * 3- Possible alternative way to get mir: tcx.mir_keys() and then convert the LocalDefId to DefId and
 * just call tcx.optimized_mir(def_id). These all should happen in the same place compiler may call
 * mir::pretty::write_mir_pretty(...)
 */

/***
 * This example is written based on "rust/src/test/run-make-fulldeps/obtain-borrowck"
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

extern crate rustc_borrowck;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

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
        // We must pass -Zpolonius so that the borrowck information is computed.
        rustc_args.push("-Zpolonius".to_owned());

        // TODO @Nima: Find the correct sysroot by yourself. for now we get it as an argument.
        // See filesearch::get_or_default_sysroot()

        let mut callbacks = CompilerCalls::default();
        // Call the Rust compiler with our callbacks.
        trace!("Calling the Rust Compiler with args: {:?}", rustc_args);
        rustc_driver::RunCompiler::new(&rustc_args, &mut callbacks).run()
    })
}

#[derive(Default)]
struct CompilerCalls;

impl rustc_driver::Callbacks for CompilerCalls {
    // In this callback we override the mir_borrowck query.
    fn config(&mut self, config: &mut Config) {
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
                    trace!("We have body for {}", def_path);
                    &body.body
                })
                .collect();

            let mut vf_mir_capnp_builder = vf_mir_builder::VfMirCapnpBuilder::new(tcx);
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
    use crate::vf_mir_capnp::body as body_cpn;
    use crate::vf_mir_capnp::vf_mir as vf_mir_cpn;
    use body_cpn::local_decl as local_decl_cpn;
    use body_cpn::mutability as mutability_cpn;
    use rustc_hir::def::DefKind;
    use rustc_middle::{mir, ty::TyCtxt};
    use tracing::trace;

    pub struct VfMirCapnpBuilder<'tcx, 'a> {
        tcx: TyCtxt<'tcx>,
        bodies: Vec<&'a mir::Body<'tcx>>,
    }

    impl<'tcx: 'a, 'a> VfMirCapnpBuilder<'tcx, 'a> {
        pub fn new(tcx: TyCtxt<'tcx>) -> VfMirCapnpBuilder {
            VfMirCapnpBuilder {
                tcx,
                bodies: Vec::new(),
            }
        }

        pub fn add_bodies(&mut self, bodies: &[&'a mir::Body<'tcx>]) {
            self.bodies.extend_from_slice(bodies)
        }

        pub fn build(&mut self) -> ::capnp::message::TypedBuilder<vf_mir_cpn::Owned> {
            let mut msg_cpn = ::capnp::message::TypedBuilder::<vf_mir_cpn::Owned>::new_default();
            let mut vf_mir_cpn = msg_cpn.init_root();
            Self::encode_mir(&self.bodies, self.tcx, vf_mir_cpn);
            msg_cpn
        }

        fn encode_mir(
            bodies: &[&mir::Body<'tcx>],
            tcx: TyCtxt<'tcx>,
            mut vf_mir_cpn: vf_mir_cpn::Builder<'_>,
        ) {
            let len = bodies
                .len()
                .try_into()
                .expect("The number of bodies cannot be stored in a Capnp message");
            let mut bodies_cpn = vf_mir_cpn.reborrow().init_bodies(len);
            for (idx, body) in bodies.iter().enumerate() {
                let mut body_cpn = bodies_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_body(body, tcx, body_cpn);
            }
        }

        fn encode_body(
            body: &mir::Body<'tcx>,
            tcx: TyCtxt<'tcx>,
            mut body_cpn: body_cpn::Builder<'_>,
        ) {
            use rustc_index::vec::Idx;

            trace!("Encoding mir: {:?}", body.source.instance);
            let def_id = body.source.def_id();
            let kind = tcx.def_kind(def_id);
            match kind {
                DefKind::Fn => {
                    let mut def_kind_cpn = body_cpn.reborrow().init_def_kind();
                    def_kind_cpn.set_fn(());
                }
                _ => std::todo!(),
            }

            let def_path = tcx.def_path_str(def_id);
            body_cpn.set_def_path(&def_path);

            let arg_count = body.arg_count.try_into().expect(&format!(
                "The number of args of {} cannot be stored in a Capnp message",
                def_path
            ));
            body_cpn.set_arg_count(arg_count);

            let local_decls_count = body.local_decls.len().try_into().expect(&format!(
                "The number of local declarations of {} cannot be stored in a Capnp message",
                def_path
            ));
            assert!(
                local_decls_count > arg_count,
                "Local declarations of {} are not more than its args",
                def_path
            );

            let mut local_decls_cpn = body_cpn.reborrow().init_local_decls(local_decls_count);
            for (idx, local_decl) in body.local_decls.iter().enumerate() {
                let mut local_decl_cpn = local_decls_cpn.reborrow().get(idx.try_into().unwrap());
                Self::encode_local_decl(local_decl, tcx, local_decl_cpn);
            }
        }

        fn encode_local_decl(
            local_decl: &mir::LocalDecl<'tcx>,
            tcx: TyCtxt<'tcx>,
            mut local_decl_cpn: local_decl_cpn::Builder<'_>,
        ) {
            let mut mutability_cpn = local_decl_cpn.reborrow().init_mutability();
            Self::encode_mutability(local_decl.mutability, mutability_cpn);

            let mut local_decl_id_cpn = local_decl_cpn.reborrow().init_id();
        }

        #[inline]
        fn encode_mutability(m: mir::Mutability, mut mutability_cpn: mutability_cpn::Builder<'_>) {
            match m {
                mir::Mutability::Mut => mutability_cpn.set_mut(()),
                mir::Mutability::Not => mutability_cpn.set_not(()),
            }
        }

        fn encode_local_decl_id() {}
    }
}

// This module should be in the crate root because the generated code counts on it
mod vf_mir_capnp {
    #![allow(unused)]
    include!(concat!(env!("OUT_DIR"), "/vf_mir_capnp.rs"));
}

mod mir_utils {
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;

    pub fn mir_def_ids(tcx: TyCtxt<'_>) -> Vec<DefId> {
        tcx.mir_keys(())
            .iter()
            .map(|local_def_id| local_def_id.to_def_id())
            .collect()
    }
}
