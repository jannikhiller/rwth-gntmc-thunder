macro_rules! check_file {
    ($file:expr $(, $is_true:expr)?) => {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file($file);
        let aps_arrays = vec![
        vec!["crit0".to_string(), "wait0".to_string()],
        vec!["some_crit".to_string()],
        vec!["crit0".to_string()],
        vec!["fair".to_string(), "crit0".to_string()]
];

        for (prop,aps) in props.iter().zip(aps_arrays) {

            assert_eq!(prop.get_aps(), aps)
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
    use thunder::parser::gntmc;

    #[test]
    fn test_peterson_ltl() {
        check_file!("./tests/peterson_ltl/peterson.2.gntmc");
    }
}
