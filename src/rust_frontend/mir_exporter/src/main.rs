mod vf_mir {

    mod vf_mir_capnp {
        #![allow(unused)]
        include!(concat!(env!("OUT_DIR"), "/src/vf_mir_capnp.rs"));
    }
    use capnp::serialize;
    use vf_mir_capnp::vf_mir;
    pub fn write_vf_mir() -> ::capnp::Result<()> {
        let mut message = ::capnp::message::Builder::new_default();
        {
            let mut vf_mir = message.init_root::<vf_mir::Builder>();
            vf_mir.set_id(200);
        }

        serialize::write_message(&mut ::std::io::stdout(), &message)
    }
}

fn main() {
    vf_mir::write_vf_mir().unwrap();
    println!();
    println!("Let us say it is MIR for now!");
}
