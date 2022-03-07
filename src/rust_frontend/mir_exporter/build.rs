fn main() {
    println!("cargo:rerun-if-changed=../vf_mir/vf_mir.capnp");
    capnpc::CompilerCommand::new()
        .src_prefix("../vf_mir")
        .file("../vf_mir/vf_mir.capnp")
        .run()
        .expect("Compiling Schema Failed");
}
