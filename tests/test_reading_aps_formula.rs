#[cfg(test)]
mod tests {
    use thunder::parser::gntmc;

    #[test]
    fn test_peterson_ltl() {
        let (_, props, _) = gntmc::parse_gntmc_file("./tests/peterson_ltl/peterson.2.gntmc");
        let aps_arrays = vec![
            vec!["crit0".to_string(), "wait0".to_string()],
            vec!["some_crit".to_string()],
            vec!["crit0".to_string()],
            vec!["fair".to_string(), "crit0".to_string()],
        ];

        for (prop, aps) in props.iter().zip(aps_arrays) {
            assert_eq!(prop.get_aps(), aps)
        }
    }
}
