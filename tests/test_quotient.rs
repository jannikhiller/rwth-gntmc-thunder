macro_rules! check_file {
    ($file:expr, $vec:expr $(, $is_true:expr)?) => {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file($file);
        for prop in props.iter() {
            match &prop.property_type {
                PropertyType::Ltl(inner_node) => {
                    let mut options = Options::new();
                    options.set_quotienting_algorithm(QuotientingAlgorithm::SimpleRefinement);
                    println!("start bisimulation quotienting with simple refinement");
                    let ts_prime = bisimulation::quotienting::quotienting(
                        &ts,
                        &options,
                        Some(&prop.get_aps()),
                    );
                    assert_eq!(ts_prime.get_states().len(), $vec[0]);
                    assert_eq!(ts_prime.get_num_transitions(), $vec[1]);
                    println!("finished quotienting with simple refinement");
                    let options_new = thunder::checker::checker::Options::new();
                    let result = check(&ts_prime, prop, &options_new);
                    let expected = check(&ts, prop, &options_new);
                    assert_eq!(result.is_ok(), expected.is_ok());

                    options.set_quotienting_algorithm(QuotientingAlgorithm::AdvancedRefinement);
                    println!("start bisimulation quotienting with advanced refinement");
                    let ts_prime_2 = bisimulation::quotienting::quotienting(
                        &ts,
                        &options,
                        Some(&prop.get_aps()),
                    );
                    println!("finished quotienting with advanced refinement");
                    let result_2 = check(&ts_prime, prop, &options_new);
                    let expected_2 = check(&ts, prop, &options_new);
                    assert_eq!(ts_prime_2.get_states().len(), $vec[0]);
                    assert_eq!(ts_prime_2.get_num_transitions(), $vec[1]);
                    assert_eq!(result_2.is_ok(), expected_2.is_ok());
                }
                _ => panic!("Wrong property type"),
            }
        }
    };
}

macro_rules! generate_res_test {
    ($($name:ident), *) => {
        $(
        #[test]
        fn $name() {
            check_file!(concat!("./tests/res/", stringify!($name), ".gntmc"));
        }
        )*
    };
}

#[cfg(test)]
mod tests {
    use thunder::bisimulation;
    use thunder::checker::checker::check;
    use thunder::checker::checker::Options;
    use thunder::checker::checker::QuotientingAlgorithm;
    use thunder::parser::gntmc;
    use thunder::property::property::PropertyType;

    #[test]
    fn test_quotient() {
        //First test-file is Exc4 of Sheet 9
        let sizes_1 = vec![9usize, 14usize];
        check_file!("./tests/quotienting/quotienting.1.gntmc", sizes_1.clone());
        //Second test-file is Exc3 a)/b) of sheet 9
        let sizes_2 = vec![5usize, 8usize];
        check_file!("./tests/quotienting/quotienting.2.gntmc", sizes_2.clone());
    }
}
