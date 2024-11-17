#[cfg(test)]
mod tests {
    use thunder::checker::invariant::bfs_invariant_checking;
    use thunder::parser::gntmc;

    fn convert_result_to_bool(prop_fulfilled: &Result<bool, (Vec<Vec<String>>, Vec<usize>)>) -> bool {
        if prop_fulfilled.is_ok() {
            true
        } else {
            false
        }
    }
    
    fn print_path_and_trace(prop_fulfilled: Result<bool, (Vec<Vec<String>>, Vec<usize>)>) -> String {
        let (path, trace) = prop_fulfilled.err().unwrap();
        format!("Failing path: {:?}\nFailing trace: {:?}", path, trace)
    }
    
    #[test]
    fn test_inv_1() {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file("./tests/res/test_inv_1.gntmc");
        for (prop, is_true) in props.iter().zip(is_trues.iter()) {
            let prop_fulfilled = bfs_invariant_checking(&ts, prop);
            
            assert_eq!(convert_result_to_bool(&prop_fulfilled), is_true.unwrap());
        }
    }

    // #[test]
    // fn test_inv_2() {
    //     let (ts, props, is_trues) = gntmc::parse_gntmc_file("./tests/res/test_inv_2.gntmc");
    //     for (prop, is_true) in props.iter().zip(is_trues.iter()) {
    //         let prop_fulfilled = bfs_invariant_checking(&ts, prop);
    // 
    //         assert_eq!(prop_fulfilled, is_true.unwrap());
    //     }
    // }

    #[test]
    fn test_inv_3() {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file("./tests/res/test_inv_3.gntmc");
        for (prop, is_true) in props.iter().zip(is_trues.iter()) {
            let prop_fulfilled = bfs_invariant_checking(&ts, prop);

            assert_eq!(convert_result_to_bool(&prop_fulfilled), is_true.unwrap());
        }
    }

    #[test]
    fn test_inv_4() {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file("./tests/res/test_inv_4.gntmc");
        for (prop, is_true) in props.iter().zip(is_trues.iter()) {
            let prop_fulfilled = bfs_invariant_checking(&ts, prop);

            assert_eq!(convert_result_to_bool(&prop_fulfilled), is_true.unwrap());
        }
    }


    #[test]
    fn test_inv_philosophers_broken() {
        for i in (3 .. 12) {
            let (ts, props, _) = gntmc::parse_gntmc_file(&format!("./tests/philosophers/philosophers-dl.{i}.gntmc"));
            for prop in props.iter() {
                let prop_fulfilled = bfs_invariant_checking(&ts, prop);

                assert_eq!(convert_result_to_bool(&prop_fulfilled), false, "Failed at philosphers number {i}.");
            }
        }
    }

    #[test]
    fn test_inv_philosophers_fixed() {
        for i in (3 .. 13) {
            let (ts, props, _) = gntmc::parse_gntmc_file(&format!("./tests/philosophers/philosophers-dl.{i}.gntmc"));
            for prop in props.iter() {
                let prop_fulfilled = bfs_invariant_checking(&ts, prop);

                assert_eq!(convert_result_to_bool(&prop_fulfilled), true,
                           "Failed at philosphers number {i}.\nFound following counterexample:\n{:?}",
                           print_path_and_trace(prop_fulfilled));
            }
        }
    }
}
