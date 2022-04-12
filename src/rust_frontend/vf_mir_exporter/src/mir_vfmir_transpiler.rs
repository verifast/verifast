use rustc_middle::mir::{self, traversal, visit::Visitor};

pub struct MirVfmirTranspiler {}

impl MirVfmirTranspiler {
    pub fn transpile(body: &mir::Body) {
        // trace!("write_mir_sig: {:?}", body.source.instance);
    }
}
