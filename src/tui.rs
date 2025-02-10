use crate::bisimulation::quotienting::quotienting;
use crate::checker::checker::{check, Options, PersistenceCheckingAlgorithm, QuotientingAlgorithm};
use crate::common::transition_system::TransitionSystem;
use crate::parser::gntmc::parse_gntmc_file;
use crate::property::property::{FormulaTreeNode, FormulaTreeNodeType, Property, PropertyType};
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

    #[arg(short, long, default_value_t, value_enum)]
    persistence: PersistenceCheckingAlgorithm,

    #[arg(short, long, default_value_t, value_enum)]
    bisimulation: QuotientingAlgorithm,
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
    println!("Meta information of model:\n\tnumber of states: {:?}\n\tnumber of transitions: {:?}\n\tnumber of initial states: {:?}\n",
        ts.get_num_states(), ts.get_num_transitions(), ts.get_initial_states().len()
    );
    (ts, props, parsing_time)
}

fn check_properties(ts: &TransitionSystem, props: &[Property<String>], options: &Options) -> f64 {
    let empty_formula = FormulaTreeNode::new(None, None, None, FormulaTreeNodeType::Atomic);
    let mut total_model_checking_time = std::time::Duration::new(0, 0);
    let mut checking_ts: &TransitionSystem = ts;
    let mut quotient_ts; // Declare outside the loop
    for (i, prop) in props.iter().enumerate() {
        if options.quotienting_algorithm != QuotientingAlgorithm::Without {
            // add function to get all aps of property
            let aps = prop.get_aps();
            println!("Performing bisimulation quotienting with given strategy");
            let pre_quot_time = std::time::Instant::now();
            quotient_ts = quotienting(ts, options, Some(&aps));
            let post_quot_time = std::time::Instant::now();
            println!(
                "Quotienting took {}s",
                (post_quot_time - pre_quot_time).as_secs_f64()
            );
            println!("Meta information of quotient:\n\tnumber of states: {:?}\n\tnumber of transitions: {:?}\n\tnumber of initial states: {:?}",
                     quotient_ts.get_num_states(), quotient_ts.get_num_transitions(), quotient_ts.get_initial_states().len()
            );
            checking_ts = &quotient_ts;
        }
        println!("Checking property {i}: {:?}...", prop.name);
        let pre_checking_time = std::time::Instant::now();
        let result = check(checking_ts, prop, options);
        let post_checking_time = std::time::Instant::now();
        println!(
            "Done. Checking took {}s",
            (post_checking_time - pre_checking_time).as_secs_f64()
        );
        total_model_checking_time += post_checking_time - pre_checking_time;
        println!(
            "Result for property {i}: {:?}: {:?}",
            prop.name,
            result.is_ok()
        );
        if result.is_err() && prop.property_type != PropertyType::Ctl(empty_formula.clone()) {
            let (trace, path) = result.err().unwrap();
            println!("\tFound following path as counterexample: {:?}", path);
            println!("\tCorresponding trace: {:?}", trace);
        }
        println!();
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

    let persistence_algorithm = args.persistence;
    let quotienting_algorithm: QuotientingAlgorithm = args.bisimulation;
    let mut options = Options::new();
    options.set_persistence_algorithm(persistence_algorithm);
    options.set_quotienting_algorithm(quotienting_algorithm);

    let checking_time = check_properties(&ts, &props, &options);

    println!("Total runtime: {:?}", parsing_time + checking_time);
}
