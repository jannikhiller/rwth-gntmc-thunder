#[cfg(test)]
mod test {
    use thunder::parser::gntmc;

    //the first test, is Exc 2 from sheet 3
    #[test]
    fn test_omega_reg_1() {
        let (_, props, _) = gntmc::parse_gntmc_file("./tests/res/test_omega_reg_1.gntmc");
        for prop in props {
            assert_eq!(["a".to_string(), "b".to_string()].to_vec(), prop.get_aps());
        }
    }
}
