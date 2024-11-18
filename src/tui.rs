use crate::checker::invariant::bfs_invariant_checking;
use crate::common::transition_system::TransitionSystem;
use crate::parser::gntmc::parse_gntmc_file;
use crate::parser::property::Property;

use clap::Parser;
use env_logger::Builder;
use log::*;
use std::io::Write;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// File in the .gntmc file format specifying the model and properties to be checked
    gntmc_file: std::path::PathBuf,

    /// Verbosity level, increase by repeating (-v -vv ...)
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
}

fn initilize_logger(verbosity: u8) {
    // Initialize the logger with the desired verbosity level
    let log_level = match verbosity {
        0 => log::LevelFilter::Warn,
        1 => log::LevelFilter::Info,
        2 => log::LevelFilter::Debug,
        _ => log::LevelFilter::Trace,
    };
    Builder::new()
        .filter(None, log_level)
        .format(|buf, record| {
            writeln!(
                buf,
                "{} [{}] - {}",
                chrono::Local::now().format("%Y-%m-%d %H:%M:%S"),
                record.level(),
                record.args()
            )
        })
        .init();
}

fn parse_model_and_properties(
    gntmc_file: &std::path::Path,
) -> (TransitionSystem, Vec<Property<String>>) {
    info!("Parsing gntmc file {:?}...", gntmc_file);
    let pre_parsing_time = std::time::Instant::now();
    let (ts, props) = parse_gntmc_file(gntmc_file.to_str().unwrap());
    let post_parsing_time = std::time::Instant::now();
    info!(
        "Done. Model building took {}s. Number of states: {}, number of transitions: {}",
        (post_parsing_time - pre_parsing_time).as_secs(),
        ts.get_num_states(),
        ts.get_num_transitions()
    );
    (ts, props)
}

fn check_properties(ts: &TransitionSystem, props: &Vec<Property<String>>) {
    let mut total_model_checking_time = std::time::Duration::new(0, 0);
    for (i, prop) in props.iter().enumerate() {
        info!("Checking property {}", i);
        let pre_checking_time = std::time::Instant::now();
        let result = bfs_invariant_checking(&ts, prop);
        let post_checking_time = std::time::Instant::now();
        total_model_checking_time += pre_checking_time - post_checking_time;
        info!(
            "Done. Checking took {}s.",
            (pre_checking_time - post_checking_time).as_secs()
        );
        print!("Result for property {i}: {result}");
    }
    info!(
        "Checked all properties. Total time {}s.",
        total_model_checking_time.as_secs()
    );
}

pub fn run() {
    let args = Cli::parse();
    initilize_logger(args.verbose);
    let (ts, props) = parse_model_and_properties(&args.gntmc_file);
    check_properties(&ts, &props);
}
