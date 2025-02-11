Thunder Model Checker
=====================

This is a university project implementing different model checking algorithms in Rust. 

Currently, the following features are implemented:
- Invariant checking using breadth first search
- Persistence checking
- Checking of regular properties (given as NFA)
- Checking of omega-regular properties (given as NBA)
- Checking of LTL-formulae
- Checking of CTL-formulae
- Bisimulation-Quotienting (simple and advanced refinement, w.r.t. some $A \subseteq 2^{AP}$)
- Visualization of the given transition system and counter-examples 

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

General information about accepted arguments can be found calling `thunder --help`.

#### Persistence Checking

For model checking regular, omega regular and LTL-based properties the default mechanism is based on nested depth-first search.
In total, four different algorithms are implemented:
- basic nested dfs using `-p nested-dfs` (default)
- improved nested dfs using `-p new-nested-dfs`
- using SCCs via Tarjan's algorithm using `-p scc`
- using SCCs via Couvreur algorithm using `-p scc-couvreur`

The implementation of the improved nested dfs and Couvreur's algorithm are based on the paper
"A Note on On-The-Fly Verification Algorithms" by Stefan Schwoon and Javier Esparza which can be found [here](https://archive.model.in.tum.de/um/bibdb/schwoon/dfs-tr.pdf).

In general, the algorithms taken from this paper may perform better than their simpler counterparts. \
Note, that both SCC-based algorithms are implemented recursively. Thus, they may produce stackoverflow errors on larger models.
To increase the stack size you can compile thunder after setting the `RUSTFLAGS="-C link-args=-Wl,-zstack-size=stackSize"` environment variable,
where `stackSize` is the size of the stack in bytes.

#### Bisimulation-Quotienting

To apply bisimulation minimization before checking the given properties, use:
```bash
-b <simple-refinement | advanced-refinement>
```

By default, bisimulation is disabled. It can be explicitly disabled using `-b without`.

#### Visualization
Currently, we support visualizing the parsed transition system by generating a `DOT`-file by adding the flag
```bash
--visualize-ts <filename>
```
during model checking. The initial states are represented by a box in this file. Note that the produced `DOT`-file has 
to be converted to, for example, a `PNG`-file to be human-readable.
Additionally, we also provide the possibility to generate a visual representation of the counter-example for each
violated property inside the given transition system by using:
```bash
--visualize-cex <filename-prefix>
```
This creates, in case of multiple violated properties, a family of files named as `filename-prefix_prop.dot`, where 
`prop` is the name of the violated property.<br />
Please note that this visualization heavily depends on the size of the given transition system.

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

#### Note
The library is only intended to enable integration tests. Therefore, we do NOT guarantee a stable interface.

### Custom Tests
`.gntmc`-files with/for custom tests can be found at `tests/res/`. \
The included python code generates a `.gntmc`-file for a transition system of given size.
A generated example is already included within the other `.gntmc`-files.

Contributers
------------
- Andreas Gerhards `andreas.gerhards@rwth-aachen.de`
- Jannik Hiller `jannik.hiller@rwth-aachen.de`
- Johannes Kurth `johannes.kurth@rwth-aachen.de`
- Peter Lindner `peter.lindner@rwth-aachen.de`
