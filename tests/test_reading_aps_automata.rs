macro_rules! check_file {
    ($file:expr $(, $is_true:expr)?) => {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file($file);
        for (prop, is_true) in props.iter().zip(is_trues.iter()) {
            assert_eq!(["a".to_string(), "b".to_string()].to_vec(), prop.get_aps());
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
    use thunder::parser::gntmc;
    //the first test, is Exc 2 from sheet 3
    generate_res_test!(test_omega_reg_1);
}
