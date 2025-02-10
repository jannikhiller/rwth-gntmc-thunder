macro_rules! check_file {
    ($file:expr $(, $is_true:expr)?) => {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file($file);
        for (prop, is_true) in props.iter().zip(is_trues.iter()) {
            let mut options_ndfs = thunder::checker::Options::new();
            options_ndfs.set_persistence_algorithm(thunder::checker::PersistenceCheckingAlgorithm::NestedDfs);
            let prop_fulfilled_ndfs = check(&ts, prop, &options_ndfs);
            let mut fail_message_ndfs = format!("Failed at file {}.", $file);

            if let Err((path, trace)) = &prop_fulfilled_ndfs {
                fail_message_ndfs.push_str(&format!(
                    "\nFound following counterexample using NDFS for property {:?}:\nFailing path: {:?}\nFailing trace: {:?}",
                    prop.name, path, trace
                ));
            }
            let expected_ndfs = is_true.unwrap_or($($is_true ||)? false);
            assert_eq!(prop_fulfilled_ndfs.is_ok(), expected_ndfs, "{}", fail_message_ndfs);

            let mut options_scc = thunder::checker::Options::new();
            options_scc.set_persistence_algorithm(thunder::checker::PersistenceCheckingAlgorithm::Scc);
            let prop_fulfilled_scc = check(&ts, prop, &options_scc);
            let mut fail_message_scc = format!("Failed at file {}.", $file);

            if let Err((path, trace)) = &prop_fulfilled_scc {
                fail_message_scc.push_str(&format!(
                    "\nFound following counterexample using SCC for property {:?}:\nFailing path: {:?}\nFailing trace: {:?}",
                    prop.name, path, trace
                ));
            }
            let expected_scc = is_true.unwrap_or($($is_true ||)? false);
            assert_eq!(prop_fulfilled_scc.is_ok(), expected_scc, "{}", fail_message_scc);
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
mod test {
    use thunder::checker::check;
    use thunder::parser::gntmc;

    generate_res_test!(test_safe_1, test_safe_2);
}
