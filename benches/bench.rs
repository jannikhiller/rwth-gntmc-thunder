use thunder::checker::*;
use thunder::common::*;
use thunder::parser::*;
use thunder::property::*;

fn main() {
    divan::main();
}

#[divan::bench(args = [
    "./tests/res/test_inv_1.gntmc",
    //"./tests/res/test_inv_2.gntmc", // This test is too slow
    "./tests/res/test_inv_3.gntmc",
    "./tests/res/test_inv_4.gntmc",
    "./tests/philosophers/philosophers-dl.9.gntmc",
    "./tests/philosophers/philosophers-dlfix.9.gntmc",
])]
fn build_model(
    file: &str,
) -> (
    transition_system::TransitionSystem,
    Vec<Property<String>>,
    Vec<Option<bool>>,
) {
    gntmc::parse_gntmc_file(file)
}

#[divan::bench(args = [
    "./tests/philosophers/philosophers-dl.9.gntmc",
    "./tests/philosophers/philosophers-dlfix.9.gntmc",
    "./tests/peterson/peterson.3.gntmc",
    "./tests/peterson_ltl/peterson.3.gntmc",
    "./tests/peterson_ctl/peterson.3.gntmc"
])]
fn checking(bencher: divan::Bencher, path: &str) {
    bencher
        .with_inputs(|| gntmc::parse_gntmc_file(path))
        .bench_values(|(ts, props, _)| {
            for prop in &props {
                let _ = divan::black_box(check(&ts, prop, &Options::default()));
            }
        })
}
