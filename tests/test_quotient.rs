#[cfg(test)]
mod tests {
    use thunder::bisimulation;
    use thunder::checker::checker::check;
    use thunder::checker::checker::Options;
    use thunder::checker::checker::QuotientingAlgorithm;
    use thunder::parser::gntmc;
    use thunder::parser::property::PropertyType;

    fn run_test(file: &str, sizes: &[usize]) {
        let (ts, props, _) = gntmc::parse_gntmc_file(file);
        for prop in props.iter() {
            match &prop.property_type {
                PropertyType::Ltl(_) => {
                    let mut options = Options::new();
                    options.set_quotienting_algorithm(QuotientingAlgorithm::SimpleRefinement);
                    println!("start bisimulation quotienting with simple refinement");
                    let ts_prime = bisimulation::quotienting::quotienting(
                        &ts,
                        &options,
                        Some(&prop.get_aps()),
                    );
                    assert_eq!(ts_prime.get_states().len(), sizes[0]);
                    assert_eq!(ts_prime.get_num_transitions(), sizes[1]);
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
                    assert_eq!(ts_prime_2.get_states().len(), sizes[0]);
                    assert_eq!(ts_prime_2.get_num_transitions(), sizes[1]);
                    assert_eq!(result_2.is_ok(), expected_2.is_ok());
                }
                _ => panic!("Wrong property type"),
            }
        }
    }

    #[test]
    fn test_quotient() {
        //First test-file is Exc4 of Sheet 9
        run_test(
            "./tests/quotienting/quotienting.1.gntmc",
            &[9usize, 14usize],
        );
        run_test("./tests/quotienting/quotienting.2.gntmc", &[5usize, 8usize]);
    }
}
