macro_rules! check_file {
    ($file:expr $(, $is_true:expr)?) => {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file($file);
        for (prop, is_true) in props.iter().zip(is_trues.iter()) {
            let mut options = thunder::checker::checker::Options::new();
            options.set_persistence_algorithm(thunder::checker::checker::PersistenceCheckingAlgorithm::NestedDfs);
            let prop_fulfilled = check(&ts, prop, &options);
            let mut fail_message = format!("Failed at file {}.", $file);

            if let Err((path, trace)) = &prop_fulfilled {
                fail_message.push_str(&format!(
                    "\nFound following counterexample:\nFailing path: {:?}\nFailing trace: {:?}",
                    path, trace
                ));
            }
            let expected = is_true.unwrap_or($($is_true ||)? false);
            assert_eq!(prop_fulfilled.is_ok(), expected, "{}", fail_message);
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
    use thunder::checker::checker::check;
    use thunder::parser::gntmc;
    generate_res_test!(test_inv_1, test_inv_2, test_inv_3, test_inv_4);

    #[test]
    fn test_inv_philosophers_broken() {
        for i in 3..12 {
            check_file!(
                &format!("./tests/philosophers/philosophers-dl.{i}.gntmc"),
                false
            );
        }
    }

    #[test]
    fn test_inv_philosophers_fixed() {
        for i in 3..13 {
            check_file!(
                &format!("./tests/philosophers/philosophers-dlfix.{i}.gntmc"),
                true
            );
        }
    }
}
