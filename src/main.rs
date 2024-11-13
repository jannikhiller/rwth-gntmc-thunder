mod checker;
mod common;
mod parser;
mod tui;

use env_logger::Env;

fn main() {
    // We default to logging on debug level for development purposes.
    #[cfg(debug_assertions)]
    env_logger::Builder::from_env(Env::default().default_filter_or("debug")).init();
    // And log on warn level for build/release purposes
    #[cfg(not(debug_assertions))]
    env_logger::init_from_env(Env::default().default_filter_or("warn"));

    tui::run();
}
