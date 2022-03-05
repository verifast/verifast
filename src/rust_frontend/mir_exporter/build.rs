fn main() {
    capnpc::CompilerCommand::new()
        .file("src/vf_mir.capnp")
        .run()
        .expect("Compiling Schema Failed");
}
