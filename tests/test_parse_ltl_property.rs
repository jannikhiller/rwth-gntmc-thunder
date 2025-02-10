#[cfg(test)]
mod tests {
    use thunder::parser::gntmc;

    #[test]
    fn test_peterson_ltl() {
        gntmc::parse_gntmc_file("./tests/res/test_ltl_parse_1.gntmc");
        gntmc::parse_gntmc_file("./tests/peterson_ltl/peterson.2.gntmc");
    }
}
