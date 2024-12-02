Thunder Model Checker
=====================

This is a university project implementing different model checking algorithms in rust. 

Currently the following algorithms are implemented:
- Invariant checking using breadth first search
- Persistence checking
- Checking of regular properties (given as NFA)
- Checking of omega-regular properties (given as NBA)

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
thunder "filepath"
```
where `"filepath"` is a path to the `gntmc`-file containing the specification of the model and properties.

You can get further information calling `thunder --help`

### Testing
```bash
cargo test
```

### Benchmarking
```bash
cargo bench
```

### Profiling
In this section we are using the `perf` tool, but you can use any other tool you like.
1. Compile the project with the profile target:
```bash
cargo build --profile=profile
```
2. Run `thunder` with `perf` and a test file:
```bash
perf record -F99 --call-graph dwarf target/profile/thunder tests/res/test_inv_2.gntmc
```
3. Convert the `perf` output to a format that (https://profiler.firefox.com/) can read:
```bash
perf script -F +pid > test.perf
```
4. Open the file in (https://profiler.firefox.com/).

## Note
The library is only intended to enable integration tests. Therefore, we do NOT guarantee a stable interface.

## Custom Tests
`.gntmc`-files with/for custom tests can be found at `tests/res/`. \
The included python code generates a `.gntmc`-file for a transition system of given size.
A generated example is already included within the other `.gntmc`-files.

Contributers
------------
- Jannik Hiller `jannik.hiller@rwth-aachen.de`
- Andreas Gerhards `andreas.gerhards@rwth-aachen.de`
- Johannes Kurth `johannes.kurth@rwth-aachen.de`
- Peter Lindner `peter.lindner@rwth-aachen.de`
