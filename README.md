# local-flags

This repository contains the software which was used to prove the results in my MSc Mathematics thesis:
TODO LINK. It contains a Rust implementation of the semidefinite method on local flags. This
framework can be used to prove asymptotic bounds on subgraph densities relative to the maximum
degree Δ(G) for Δ(G) large.

In particular:
- `examples/strong_edge_colouring.rs`: Proves the best known bound on the Erdős and Nešetřil
  conjecture on strong edge colouring[^erdosnes].
- `examples/bipartite_strong_edge_colouring.rs`. Proves the best known bound for the
  bipartite special case conjectured by Faudree et al[^erdosnes].
- `examples/bounded_pentagon.rs`: Proves a decent upper bound on the number of pentagons in a
  triangle free Δ-regular graph.
- `examples/bounded_pentagon_alt_approach.rs`: Proves a stronger upper bound on the same problem.

You can find the certificates of these programs for reference in the `certificates/` directory.

[^erdosnes]: *Induced matchings in bipartite graphs*, Faudree, R. J., Gyárfas, A., Schelp, R. H., & Tuza, Zs. (1989). Discrete Mathematics, 78(1–2), 83–87. https://doi.org/10.1016/0012-365X(89)90163-5

## Dependencies

You need to have the `csdp` command line installed to solve semi-definite optimization problems.
```
sudo apt install cmake gfortran coinor-csdp
```

This code relies on a slight modification of the
[`rust-flag-algebra` package](https://crates.io/crates/flag-algebra)
found at https://github.com/EoinDavey/rust-flag-algebra.

## Usage

To run one of the examples of the `example/` folder, for instance `example/bounded_pentagon.rs`.
```
cargo run --release --example bounded_pentagon
```
The first compilation may be quite long. The first execution can also take time because the library needs to compute lists of graphs and the matrices of some flag operators. These later are stored in files for later computations. Eventually, the bottleneck is the SDP solver.
