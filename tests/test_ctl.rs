macro_rules! check_file {
    ($file:expr $(, $is_true:expr)?) => {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file($file);

        for prop in props.iter() {
            match &prop.property_type {
                PropertyType::Ctl(inner_node) => {
                    println!("{}", inner_node)
                }
                _ => panic!("Wrong property type"),
            }

            let mut options = thunder::checker::checker::Options::new();
            let prop_fulfilled = check(&ts, prop, &options);
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
    use thunder::property::property::PropertyType;
    generate_res_test!(test_ctl_1, test_ctl_2);
}
