fn private() {
    println!("This should be a private message");
}

pub fn public() {
    private();
    println!("This should be a public message");
}
