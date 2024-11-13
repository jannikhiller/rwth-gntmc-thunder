use clap::Parser;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Cli {
    /// File in the .gntmc file format specifying the model and properties to be checked
    gntmc_file: std::path::PathBuf,

    // Verbosity level, increase by repeating (-v -vv ...)
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,
}

pub fn run() {
    let args = Cli::parse();
    println!(
        "file: {:?}, verbosity level: {:?}",
        args.gntmc_file, args.verbose
    );
}
