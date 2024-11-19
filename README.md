Thunder Model Checker
=====================

This is a university project implementing different model checking algorithms in rust. 

Currently the following algorithms are implemented:
- Invariant checking using breadth first search

Requirements
------------
- Rust 1.82.0
- Cargo

Usage
-----
### Building
```bash
cargo build
```

To compile with optimizations use `cargo build --release`.

### Execution
```bash
cargo run "filepath"
```
OR (after build/install)
```bash
thunder "filepath
```
where `"filepath"` is a path to the `gntmc`-file containing the specification of the model and properties.

You can get further information calling `thunder --help`

### Testing
```bash
cargo test
```

## Note
The library is only intended to enable integration tests. Therefore, we do NOT guarantee a stable interface.

Contributers
------------
- Jannik Hiller `jannik.hiller@rwth-aachen.de`
- Andreas Gerhards `andreas.gerhards@rwth-aachen.de`
- Johannes Kurth `johannes.kurth@rwth-aachen.de`
- Peter Lindner `peter.lindner@rwth-aachen.de`
