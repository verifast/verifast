#![feature(rustc_private)]

fn init_tracing() {
    // A builder for `FmtSubscriber`.
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        // All compiler prompts go to stderr
        .with_writer(std::io::stderr)
        // All spans/events with a level higher than TRACE (e.g, debug, info, warn, etc.)
        .with_max_level(tracing::Level::TRACE)
        // Completes the builder.
        .finish();

    tracing::subscriber::set_global_default(subscriber).expect("Setting default subscriber failed");
}

fn main() -> std::process::ExitCode {
    use vf_mir_exporter::*;
    init_tracing();

    run_compiler()
}
