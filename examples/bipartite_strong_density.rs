#![allow(unused_must_use, unused_variables)]
extern crate flag_algebra;
extern crate local_flags;

use flag_algebra::flags::{CGraph, Colored};
use flag_algebra::*;
use local_flags::Degree;
use num::pow::Pow;

use std::iter::once;

// ## I - Flag definition

// # Defining the type `G` of flags used
// We use Edge- and Vertex-colored Graphs
// with vertices colored with 4 colors for the vertices (0, 1, 2, 3)
// and 3 colors for the edges (0, 1, 2 where 0 means "no edge")
type G = Colored<CGraph<3>, 4>;

// # Color Names
// Colors of vertices
// Bipartite components are (0, 2) and (1, 3).
const COMPS: [[u8; 2]; 2] = [[0, 2], [1, 3]];
const X_COLS: [u8; 2] = [0, 1];
const Y_COLS: [u8; 2] = [2, 3];

// Colors of edges (0 means non-edge)
const EDGE: u8 = 1; // The edges to color
const SHADOW_EDGE: u8 = 2; // The other edges

// Ternary search precision
const EPS: f64 = 1e-4;

// # Restricting to a subclass `F`
// To reduce the combinatorial explosion, we consider only subgraph where
// * Shadow edges are all in E(X, Y)
// * Connected components each contain an element of X
#[derive(Debug, Clone, Copy)]
pub enum StrongDensityFlag {}
type F = SubClass<G, StrongDensityFlag>; // `F` is the type of restricted flags

// Implementation of the subclass
impl SubFlag<G> for StrongDensityFlag {
    // Name of the subclass (mainly used to name the memoization folder in data/)
    const SUBCLASS_NAME: &'static str = "Bipartite Strong density graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        if !flag.is_connected_to(|i| X_COLS.contains(&flag.color[i])) {
            return false;
        }
        // Bipartite check.
        for u in 0..flag.size() {
            for v in 0..u {
                if flag.edge(u, v) == 0 {
                    continue;
                }
                for comp in COMPS {
                    if comp.contains(&flag.color[u]) && comp.contains(&flag.color[v]) {
                        return false;
                    }
                }
            }
        }
        true
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

fn degenerated_strong_degree(t: Type<F>) -> V {
    assert_eq!(t.size, 2); // t is the type of an edge
    let basis = Basis::new(4).with_type(t);
    basis.qflag_from_indicator(|g: &F, _| {
        assert!(g.is_edge(0, 1));
        g.edge(2, 3) == EDGE && connected_edges(g, &[0, 1], &[2, 3])
    })
}

fn degree_in_neighbourhood(t: Type<F>) -> V {
    assert_eq!(t.size, 2);
    let basis = Basis::new(4).with_type(t);
    basis.qflag_from_indicator(|g: &F, _| {
        (X_COLS.contains(&g.content.color[2]) || X_COLS.contains(&g.content.color[3]))
            && g.edge(2, 3) == EDGE
            && connected_edges(g, &[0, 1], &[2, 3])
    })
}

fn objective(n: usize, xx_edge: Type<F>, xy_edges: [Type<F>; 2]) -> V {
    return xy_edges
        .into_iter()
        .chain(once(xx_edge))
        .map(|edge| {
            (degree_in_neighbourhood(edge) * Degree::extension(edge, 0).pow(n - 4)).untype()
        })
        .reduce(|a, b| a + b)
        .unwrap()
        * 0.25;
}

// The type corresponding to a (non-shadow) edge with vertices colored  `color1` and `color2`
fn edge_type(color1: u8, color2: u8) -> Type<F> {
    let e: F = Colored::new(CGraph::new(2, &[((0, 1), EDGE)]), vec![color1, color2]).into();
    assert!(StrongDensityFlag::is_in_subclass(&e.content));
    Type::from_flag(&e)
}

// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is in X
fn extension_in_x(t: Type<F>) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(|g: &F, type_size| X_COLS.contains(&g.content.color[type_size]))
        .named(format!("ext_in_x({{{}}})", t.print_concise()))
}

// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is black
fn extension_in_black(t: Type<F>) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(|g: &F, type_size| g.content.color[type_size] == 0)
        .named(format!("ext_in_black({{{}}})", t.print_concise()))
}

// TODO Refactor w/ black & X case
// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is red
fn extension_in_red(t: Type<F>) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(|g: &F, type_size| g.content.color[type_size] == 0)
        .named(format!("ext_in_red({{{}}})", t.print_concise()))
}

// Equalities expressing that extensions in X have twice the weight of extensions through an edge
fn size_of_x(n: usize) -> Vec<Ineq<N, F>> {
    let mut res = Vec::new();
    for t in Type::types_with_size(n - 1) {
        let diff_x = Degree::extension(t, 0) - extension_in_x(t) * 0.5;
        let diff_b = Degree::extension(t, 0) - extension_in_black(t);
        let diff_r = Degree::extension(t, 0) - extension_in_red(t);
        res.push(diff_x.equal(0.).untype());
        res.push(diff_b.equal(0.).untype());
        res.push(diff_r.equal(0.).untype());
    }
    res
}

fn ones(n: usize, k: usize, col: u8) -> V {
    Degree::project(&Colored::new(CGraph::empty(k), vec![col; k]).into(), n)
}

fn solve(n: usize, eta: N) -> N {
    let basis = Basis::<F>::new(n);

    let xx_edge = edge_type(X_COLS[0], X_COLS[1]);
    let xy_edges: [Type<F>; 2] = [
        edge_type(X_COLS[0], Y_COLS[1]),
        edge_type(X_COLS[1], Y_COLS[0]),
    ];

    // Linear constraints
    let mut ineqs = vec![
        flags_are_nonnegative(basis), // F >= 0 for every flag
    ];

    // 1. The graph of non-shadow edges is not (2 - η)∆²-degenerated
    for edge in xy_edges.into_iter().chain(once(xx_edge)) {
        let ext: V = Degree::extension(edge, 0);
        let v1 = (degenerated_strong_degree(edge) - ext.pow(2) * 2. * (2. - eta)) * ext.pow(n-4);
        ineqs.push(v1.non_negative().untype());
    }

    // 2. Every vertex has same degree ∆
    ineqs.append(&mut Degree::regularity(basis));

    ineqs.append(&mut size_of_x(n));
    for i in 1..=n {
        ineqs.push(ones(n, i, 0).untype().equal(1.));
        ineqs.push(ones(n, i, 1).untype().equal(1.));
    }

    // Assembling the problem
    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(), // Use all Cauchy-Schwarz inequalities with a matching size
        obj: -objective(n, xx_edge, xy_edges),
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "bipartite_strong_density");
    f.init();
    f.print_report(); // Write some informations in report.html

    let sprs = -f.optimal_value.unwrap();
    let sig = 1. - (sprs / 2.);

    let chi_f = 2. * (1. - (sig / 2. - sig.pow(3. / 2.) / 6.));
    let chi_rest = 2. - eta;

    let chi = f64::max(chi_f, chi_rest);

    println!("η: {:.4}\ts: {:.4}\tσ: {:.4}\tΧ': {:.4}\tΧ: {:.4}", eta, sprs, sig, chi_f, chi);
    chi
}

pub fn main() {
    init_default_log();

    let n = 5;

    println!("Begin ternary search");
    let mut eta_l = 0.3;
    let mut eta_r = 0.5;
    while f64::abs(eta_l - eta_r) > EPS {
        println!("Search Range: [{:.4}, {:.4}]; Gap {}", eta_l, eta_r, f64::abs(eta_l - eta_r));
        let l_pt = eta_l + (eta_r - eta_l)/3.;
        let r_pt = eta_l + 2.*(eta_r - eta_l)/3.;

        let l_opt = solve(n, l_pt);
        let r_opt = solve(n, r_pt);

        if l_opt < r_opt {
            eta_r = r_pt;
        } else {
            eta_l = l_pt;
        }
    }
    println!("Optimum: [{:.4}, {:.4}]", eta_l, eta_r);
}
