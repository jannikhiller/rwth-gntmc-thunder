#[cfg(test)]
mod tests {
    use thunder::checker::invariant::bfs_invariant_checking;
    use thunder::parser::gntmc;

    #[test]
    fn test_inv_1() {
        let (ts, props, is_trues) = gntmc::parse_gntmc_file("./res/test_inv_1.gntmc");
        for (prop, is_true) in props.iter().zip(is_trues.iter()) {
            let prop_fulfilled = bfs_invariant_checking(&ts, prop);
            
            assert_eq!(prop_fulfilled, is_true.unwrap());
        }
    }
}
