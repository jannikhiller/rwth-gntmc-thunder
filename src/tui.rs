use crate::checker::invariant::bfs_invariant_checking;
use crate::common::transition_system::TransitionSystem;
use crate::parser::gntmc::parse_gntmc_file;
use crate::parser::property::Property;

use clap::Parser;
use env_logger::Builder;
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

fn initialize_logger(verbosity: u8) {
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
) -> (TransitionSystem, Vec<Property<String>>, f64) {
    println!("Parsing gntmc file {:?}...", gntmc_file);
    let pre_parsing_time = std::time::Instant::now();
    let (ts, props, _) = parse_gntmc_file(gntmc_file.to_str().unwrap());
    let post_parsing_time = std::time::Instant::now();
    let parsing_time = (post_parsing_time - pre_parsing_time).as_secs_f64();
    println!("Done. Model building took {}s", parsing_time);
    println!("Meta information of model:\n\tnumber of states: {:?}\n\tnumber of transitions: {:?}\n\tnumber of initial states: {:?}",
        ts.get_num_states(), ts.get_num_transitions(), ts.get_initial_states().len()
    );
    (ts, props, parsing_time)
}

fn check_properties(ts: &TransitionSystem, props: &[Property<String>]) -> f64 {
    let mut total_model_checking_time = std::time::Duration::new(0, 0);
    for (i, prop) in props.iter().enumerate() {
        println!("Checking property {i}: {:?}...", prop.name);
        let pre_checking_time = std::time::Instant::now();
        let result = bfs_invariant_checking(ts, prop);
        let post_checking_time = std::time::Instant::now();
        println!(
            "Done. Checking took {}s",
            (pre_checking_time - post_checking_time).as_secs_f64()
        );
        total_model_checking_time += post_checking_time - pre_checking_time;
        println!(
            "Result for property {i}: {:?}: {:?}",
            prop.name,
            result.is_ok()
        );
        if result.is_err() {
            let (path, trace) = result.err().unwrap();
            println!("\tFound following path as counterexample: {:?}", path);
            println!("\tCorresponding trace: {:?}", trace);
        }
    }
    println!(
        "Checked all properties. Total time for checking: {}s",
        total_model_checking_time.as_secs_f64()
    );

    total_model_checking_time.as_secs_f64()
}

pub fn run() {
    let args = Cli::parse();
    initialize_logger(args.verbose);
    let (ts, props, parsing_time) = parse_model_and_properties(&args.gntmc_file);
    let checking_time = check_properties(&ts, &props);

    println!("Total runtime: {:?}", parsing_time + checking_time);
}
