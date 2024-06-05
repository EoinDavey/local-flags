use canonical_form::Canonize;
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use local_flags::{vertex_orbits, Degree};
use num::pow::Pow;
use std::iter::once;

// ## I - Flag definition

// # Defining the type `G` of flags used
// We use Edge- and Vertex-colored Graphs
// with vertices colored with 4 colors for the vertices (0, 1, 2, 3)
// and 3 colors for the edges (0, 1, 2 where 0 means "no edge")
type G = Colored<Graph, 4>;

// # Color Names
// Colors of vertices
// Bipartite components are (0, 2) and (1, 3).
// Component 0 has degree Δ, component 1 has degree pΔ.
const COMP: [u8; 4] = [0, 1, 0, 1];
const X_COLS: [u8; 2] = [0, 1];
const Y_COLS: [u8; 2] = [2, 3];

// The ratio between the regularity of the two components:
// Δ(B) = PΔ(A) where G = A ∪ B, Δ(A) = Δ(G).
const P: f64 = 0.5;

#[derive(Debug, Clone, Copy)]
pub enum BPStrongDensityFlag {}
type F = SubClass<G, BPStrongDensityFlag>; // `F` is the type of restricted flags

// Implementation of the subclass
impl SubFlag<G> for BPStrongDensityFlag {
    // Name of the subclass (mainly used to name the memoization folder in data/)
    const SUBCLASS_NAME: &'static str = "Bipartite Strong Density graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        if !flag.is_connected_to(|i| X_COLS.contains(&flag.color[i])) {
            return false;
        }
        // Graph is bipartite
        if flag
            .content
            .edges()
            .any(|(u, v)| COMP[flag.color[u] as usize] == COMP[flag.color[v] as usize])
        {
            return false;
        }
        true
    }
}

// ## II - Problem definition

type N = f64; // Scalar field used
type V = QFlag<N, F>; // Vectors of the flag algebra (quantum flags)

// Returns whether `e1` and `e2` are adjacent in `L(G)^2`
#[allow(non_snake_case)]
fn connected_in_L2(g: &F, e1: &[usize; 2], e2: &[usize; 2]) -> bool {
    e1.iter().any(|u1| e2.iter().any(|u2| g.is_edge(*u1, *u2)))
}

fn degree_in_neighbourhood(t: Type<F>) -> V {
    assert_eq!(t.size, 2);
    let basis = Basis::new(4).with_type(t);
    basis.qflag_from_indicator(|g: &F, _| {
        (X_COLS.contains(&g.content.color[2]) || X_COLS.contains(&g.content.color[3]))
            && g.is_edge(2, 3)
            && connected_in_L2(g, &[0, 1], &[2, 3])
    })
}

// The type corresponding to a (non-shadow) edge with vertices colored  `color1` and `color2`
fn edge_flag(color1: u8, color2: u8) -> F {
    let e: F = Colored::new(Graph::new(2, &[(0, 1)]), vec![color1, color2]).into();
    assert!(BPStrongDensityFlag::is_in_subclass(&e.content));
    return e;
}

// The type corresponding to a (non-shadow) edge with vertices colored  `color1` and `color2`
fn edge_type(color1: u8, color2: u8) -> Type<F> {
    Type::from_flag(&edge_flag(color1, color2))
}

// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is
// of the supplied colour.
fn extension_in_color(t: Type<F>, color: u8) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(move |g: &F, type_size| g.content.color[type_size] == color)
}

// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is black
fn extension_in_black(t: Type<F>) -> V {
    extension_in_color(t, 0).named(format!("ext_in_black({{{}}})", t.print_concise()))
}

// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is red
fn extension_in_red(t: Type<F>) -> V {
    extension_in_color(t, 1).named(format!("ext_in_red({{{}}})", t.print_concise()))
}

// Returns an extension vector which has the property that Φ(ext) = 1
fn unit_extension(t: Type<F>) -> V {
    let b: Basis<F> = Basis::new(t.size);
    let type_flag: &F = &b.get()[t.id].canonical();
    if COMP[type_flag.content.color[0] as usize] == 0 {
        return Degree::extension(t, 0);
    }
    assert!(COMP[type_flag.content.color[0] as usize] == 1);
    return Degree::extension(t, 0) * (1. / P);
}

fn objective(n: usize, xx_edge: Type<F>, xy_edges: [Type<F>; 2]) -> V {
    return xy_edges
        .into_iter()
        .chain(once(xx_edge))
        .map(|edge| (degree_in_neighbourhood(edge) * unit_extension(edge).pow(n - 4)).untype())
        .reduce(|a, b| a + b)
        .unwrap();
}

// Equalities expressing that extensions in X have twice the weight of extensions through an edge
fn size_of_x(n: usize) -> Vec<Ineq<N, F>> {
    let mut res = Vec::new();
    for t in Type::types_with_size(n - 1) {
        let diff_b = unit_extension(t) - extension_in_black(t) * (1. / P);
        let diff_r = unit_extension(t) - extension_in_red(t);
        res.push(diff_b.untype().equal(0.));
        res.push(diff_r.untype().equal(0.));
    }
    res
}

fn ones(n: usize, k: usize, col: u8) -> V {
    let bk: F = Colored::new(Graph::empty(k), vec![col; k]).into();
    let t: Type<F> = Type::from_flag(&bk);
    let ext = unit_extension(t);
    flag_typed(&bk, k) * ext.pow(n - k)
}

fn asymmetric_regularity(n: usize) -> Vec<Ineq<f64, F>> {
    let b: Basis<F> = Basis::new(n - 1);
    let flags = b.get();
    let mut res = Vec::new();
    for (id, flag) in flags.iter().enumerate() {
        assert!(flag == &flag.canonical());
        let orbits = vertex_orbits(flag);
        if orbits.len() < 2 {
            continue;
        }
        let t: Type<F> = Type::new(n - 1, id);
        for i in 0..orbits.len() {
            for j in 0..i {
                let ext_i: V = Degree::extension(t, i);
                let coef_i = if COMP[flag.content.color[i] as usize] == 0 {
                    1.
                } else {
                    1. / P
                };
                let ext_j: V = Degree::extension(t, j);
                let coef_j = if COMP[flag.content.color[j] as usize] == 0 {
                    1.
                } else {
                    1. / P
                };
                res.push((ext_i * coef_i - ext_j * coef_j).untype().equal(0.));
            }
        }
    }
    res
}

fn solve(n: usize) -> N {
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

    // 2. Every vertex has same degree ∆
    ineqs.append(&mut asymmetric_regularity(n));

    ineqs.append(&mut size_of_x(n));
    ineqs.push(ones(n, 1, 0).untype().equal(P));
    ineqs.push(ones(n, 1, 1).untype().equal(1.));

    // Assembling the problem
    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(), // Use all Cauchy-Schwarz inequalities with a matching size
        obj: -objective(n, xx_edge, xy_edges),
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "asymmetric_bipartite_bruhn_joos");
    f.init();
    f.print_report(); // Write some informations in report.html

    let sprs = -f.optimal_value.unwrap();
    sprs
}

pub fn main() {
    init_default_log();
    assert!(0. < P && P <= 1.);

    let n = 5;

    // Δ(H) = 2P Δ(G)²
    let sprs = solve(n); // |E| ≤ sprs/4 Δ(G)⁴
    let bound = sprs / (8. * P * P); // |E| ≤ bound (Δ(H) C 2)
    let sig = 1. - bound; // |E| ≤ (1-σ) (Δ(H) C 2)
    let eps = sig / 2. - sig.pow(3. / 2.) / 6.;
    let chi_h = 1. - eps; // χ(H) ≤ (1-ε(σ))Δ(H)
    let chi = 2. * chi_h; // χ(H) ≤ 2(1-ε(σ))Δ(G)(PΔ(G)) = 2(1-ε(σ))Δ(A)Δ(B)
    println!("sprs: {sprs:.4}, σ: {sig:.4}, ε(σ): {eps:.4}, χ(H): {chi_h:.4}, χ: {chi:.4}");
}
