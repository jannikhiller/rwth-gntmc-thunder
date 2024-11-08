use env_logger::Env;
use log::*;


fn main() {
    // We default to logging on debug level for development purposes.
    #[cfg(debug_assertions)]
    env_logger::Builder::from_env(Env::default().default_filter_or("debug")).init();
    // And log on warn level for build/release purposes
    #[cfg(not(debug_assertions))]
    env_logger::init_from_env(Env::default().default_filter_or("warn"));

    error!("This is an error log");
    warn!("This is a warn log");
    info!("This is an info log");  // This is only printed during development
    debug!("This is a debug log"); // This is only printed during development
    trace!("This is a trace log"); // This is never printed


    println!("Hello World!");
}
