#![allow(unused_must_use, unused_variables)]
extern crate flag_algebra;
extern crate local_flags;

use flag_algebra::flags::{CGraph, Colored};
use flag_algebra::*;
use local_flags::Degree;
use num::pow::Pow;

// ## I - Flag definition

// # Defining the type `G` of flags used
// We use Edge- and Vertex-colored Graphs
// with vertices colored with 2 colors for the vertices (0 and 1)
// and 3 colors for the edges (0, 1, 2 where 0 means "no edge")
type G = Colored<CGraph<3>, 2>;

// # Color Names
// Colors of vertices
const X: u8 = 0;
const Y: u8 = 1;
// Colors of edges (0 means non-edge)
const EDGE: u8 = 1; // The edges to color
const SHADOW_EDGE: u8 = 2; // The other edges
const EPS: f64 = 1e-4;

// # Restricting to a subclass `F`
// To reduce the combinatorial explosion, we consider only subgraph where
// * Shadow edges are all in E(X, Y)
// * Connected components each contain an element of X
#[derive(Debug, Clone, Copy)]
pub enum StrongDensityFlag {}
type F = SubClass<G, StrongDensityFlag>; // `F` is the type of restricted flags

// Returns `true` if every shadow edge is in E(X, Y)
fn shadow_edges_are_from_x_to_y(flag: &G) -> bool {
    for u1 in 0..flag.size() {
        for u2 in 0..u1 {
            if flag.edge(u1, u2) == SHADOW_EDGE {
                match (flag.color[u1], flag.color[u2]) {
                    (X, X) | (Y, Y) => return false,
                    _ => (),
                }
            }
        }
    }
    true
}

// Implementation of the subclass
impl SubFlag<G> for StrongDensityFlag {
    // Name of the subclass (mainly used to name the memoization folder in data/)
    const SUBCLASS_NAME: &'static str = "Strong density graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        flag.is_connected_to(|i| flag.color[i] == X) && // components intersects X
            shadow_edges_are_from_x_to_y(flag) // Shadow edges are in E(X, Y)
    }
}

// ## II - Problem definition

type N = f64; // Scalar field used
type V = QFlag<N, F>; // Vectors of the flag algebra (quantum flags)

// Returns wether `e1` and `e2` are adjacent in `L(g)^2`
fn connected_edges(g: &F, e1: &[usize; 2], e2: &[usize; 2]) -> bool {
    for &u1 in e1 {
        for &u2 in e2 {
            if g.is_edge(u1, u2) {
                return true;
            }
        }
    }
    false
}

// scaled by Delta^2/2
fn degenerated_strong_degree(t: Type<F>) -> V {
    assert_eq!(t.size, 2); // t is the type of an edge
    let basis = Basis::new(4).with_type(t);
    basis.qflag_from_indicator(|g: &F, _| {
        assert!(g.is_edge(0, 1));
        g.edge(2, 3) == EDGE && connected_edges(g, &[0, 1], &[2, 3])
    })
}

// S(t)
fn degree_in_neighbourhood(t: Type<F>) -> V {
    assert_eq!(t.size, 2);
    let basis = Basis::new(4).with_type(t);
    basis.qflag_from_indicator(|g: &F, _| {
        (g.content.color[2] == X || g.content.color[3] == X)
            && g.edge(2, 3) == EDGE
            && connected_edges(g, &[0, 1], &[2, 3])
    })
}

// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is in X
fn extension_in_x(t: Type<F>) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(|g: &F, type_size| g.content.color[type_size] == X)
        .named(format!("ext_in_x({{{}}})", t.print_concise()))
}

// Equalities expressing that extensions in X have twice the weight of extensions through an edge
fn size_of_x(n: usize) -> Vec<Ineq<N, F>> {
    let mut res = Vec::new();
    for t in Type::types_with_size(n - 1) {
        let diff = Degree::extension(t, 0) - extension_in_x(t) * 0.5;
        res.push(diff.equal(0.).multiply_and_unlabel(Basis::new(n)));
    }
    res
}

// The type corresponding to a (non-shadow) edge with vertices colored  `color1` and `color2`
fn edge_type(color1: u8, color2: u8) -> Type<F> {
    let e: F = Colored::new(CGraph::new(2, &[((0, 1), EDGE)]), vec![color1, color2]).into();
    Type::from_flag(&e)
}

fn solve(eta: f64, basis: Basis<F>, n: usize, xy_edge: Type<F>, obj: &V) -> f64 {
    // Linear constraints
    let mut ineqs = vec![
        flags_are_nonnegative(basis), // F >= 0 for every flag
    ];

    // 1. The graph of non-shadow edges of E(X, Y) are not (2 - η)∆²-degenerated
    let ext: V = Degree::extension(xy_edge, 0);
    let v1 = degenerated_strong_degree(xy_edge) - &ext * &ext * 2. * (2. - eta);
    ineqs.push(v1.non_negative().multiply_and_unlabel(basis));

    // 2. Every vertex has same degree ∆
    ineqs.append(&mut Degree::weaker_regularity(basis, 3));

    // 3. X has size at most 2∆, expressed with the two following constraints
    // 3.1. The size of X is twice the degree of any vertex
    ineqs.append(&mut size_of_x(n));

    // 3.2. The number of n-flags included in X is at most (2∆ choose n) ≈ 2^n * (∆ choose n)
    let flag_in_x =
        basis.qflag_from_indicator(|g: &F, _| g.content.color.iter().all(|&c| c == X));
    ineqs.push(flag_in_x.at_most(2.pow(n) as f64));

    // Assembling the problem
    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(), // Use all Cauchy-Schwarz inequalities with a matching size
        obj: -obj.clone(),
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "strong_density");
    f.init();
    f.print_report(); // Write some informations in report.html

    let sprs = -f.optimal_value.unwrap();

    let sig = 1.-(sprs/2.);

    let chi_f = 2. * (1.-(sig/2. - sig.pow(3./2.)/6.));
    let chi_rest = 2.-eta;

    let chi = f64::max(chi_f, chi_rest);
    println!("η: {:.4}\ts: {:.4}\tσ: {:.4}\tΧ': {:.4}\tΧ: {:.4}", eta, sprs, sig, chi_f, chi);

    chi
}

pub fn main() {
    init_default_log();

    let n = 4; // Can be pushed to 5
    let basis = Basis::new(n);

    let xy_edge = edge_type(X, Y);
    let xx_edge = edge_type(X, X);

    // Objective function
    let obj = (degree_in_neighbourhood(xy_edge) * Degree::extension(xy_edge, 0).pow(n - 4))
        .untype()
        * 0.25
        + (degree_in_neighbourhood(xx_edge) * Degree::extension(xx_edge, 0).pow(n - 4)).untype()
            * 0.125;

    // Ternary search
    println!("Begin ternary search");
    let mut eta_l = 0.;
    let mut eta_r = 0.9;
    while f64::abs(eta_l - eta_r) > EPS {
        println!("Search Range: [{:.4}, {:.4}]; Gap {}", eta_l, eta_r, f64::abs(eta_l - eta_r));
        let l_pt = eta_l + (eta_r - eta_l)/3.;
        let r_pt = eta_l + 2.*(eta_r - eta_l)/3.;

        let l_opt = solve(l_pt, basis, n, xy_edge, &obj);
        let r_opt = solve(r_pt, basis, n, xy_edge, &obj);

        if l_opt < r_opt {
            eta_r = r_pt;
        } else {
            eta_l = l_pt;
        }
    }
    println!("Optimum: [{:.4}, {:.4}]", eta_l, eta_r);
    // solve(0.2703, basis, n, xy_edge, &obj);
}
