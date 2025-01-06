macro_rules! check_file {
    ($file:expr $(, $is_true:expr)?) => {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file($file);

        for prop in props.iter() {
            println!("{:?}", prop);
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
    generate_res_test!(test_ctl_parse_1);

    #[test]
    fn test_peterson_ltl() {
        check_file!("./tests/peterson_ctl/peterson.2.gntmc");
    }
}
