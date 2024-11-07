use env_logger::Env;
use log::*;


fn main() {
    // We default to logging on debug level; at least for development purposes.
    // We can later configure this using macros depending on development or building
    env_logger::Builder::from_env(Env::default().default_filter_or("debug")).init();

    error!("This is an error log");
    warn!("This is a warn log");
    info!("This is an info log");
    debug!("This is a debug log");
    trace!("This is a trace log");


    println!("Hello World!");
}
