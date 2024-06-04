/// Bound the strong neighbourhood density for G bipartite and Δ regular.
/// Modified from bruhn_joos.rs
use canonical_form::Canonize;
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::{equal, iproduct, Itertools};
use local_flags::Degree;

// ## I - Flag definition
// We use 4 coloured graphs. Black and red represent neighbours of
// the fixed edge. The other colours represent the rest of each component.
type G = Colored<Graph, 4>;
// Bipartite components are (0, 2) and (1, 3).
const COMP: [u8; 4] = [0, 1, 0, 1];
// Colours 0, 1 correspond to the X set (those adjacent to our fixed edge).
// 2 and 3 correspond to Y, the other vertices.
const X_COLS: [u8; 2] = [0, 1];
const Y_COLS: [u8; 2] = [2, 3];

#[derive(Debug, Clone, Copy)]
pub enum BipartStrongDensityGraph {}
type F = SubClass<G, BipartStrongDensityGraph>;

type N = f64;
type V = QFlag<N, F>;

impl SubFlag<G> for BipartStrongDensityGraph {
    const SUBCLASS_NAME: &'static str = "Bipartite Strong Density Graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        // Each connected component contains a vertex colored 0 or 1
        if !flag.is_connected_to(|i| X_COLS.contains(&flag.color[i])) {
            return false;
        }
        // Graph is bipartite
        if flag.content.edges().any(|(u, v)| COMP[flag.color[u] as usize] == COMP[flag.color[v] as usize]) {
            return false;
        }
        true
    }
}

// Returns whether `e1` and `e2` are adjacent in `L(G)^2`
#[allow(non_snake_case)]
fn connected_in_L2(g: &F, e1: &[usize; 2], e2: &[usize; 2]) -> bool {
    e1.iter().any(|u1| e2.iter().any(|u2| g.is_edge(*u1, *u2)))
}

// The three ways to split a 4-elements set into two parts of size 2
const SPLIT: [([usize; 2], [usize; 2]); 3] = [([0, 1], [2, 3]), ([0, 2], [1, 3]), ([0, 3], [1, 2])];

// How many disjoint edges in g are connected in L(G)².
fn pair_count(g: &F) -> N {
    assert!(g.size() == 4);
    return SPLIT
        .iter()
        .filter(|(e1, e2)| {
            g.content.content.edge(e1[0], e1[1])
                && g.content.content.edge(e2[0], e2[1])
                && (e1.iter().any(|&v| X_COLS.contains(&g.content.color[v])))
                && (e2.iter().any(|&v| X_COLS.contains(&g.content.color[v])))
                && connected_in_L2(g, e1, e2)
        })
        .count() as f64;
}

fn ones(n: usize, k: usize, col: u8) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![col; k]).into(), n)
}

pub fn main() {
    init_default_log();
    let n = 5; // Can be pushed higher for better bounds
    assert!(n >= 4);

    let basis: Basis<F> = Basis::new(n);

    let mut sum: V = basis.zero();
    for f in Basis::<F>::new(4).get().iter() {
        let cnt = pair_count(f);
        if cnt == 0. {
            continue;
        }
        let aut_count = f.canonical().automorphisms().count() as f64;

        let typed: V = Degree::project(f, n);

        sum = sum + typed.untype() * (24. / aut_count) * cnt;
    }

    let mut ineqs = vec![flags_are_nonnegative(basis)];
    for i in 1..=n {
        ineqs.push(ones(n, i, 0).untype().at_most(1.));
        ineqs.push(ones(n, i, 1).untype().at_most(1.));
    }
    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -sum,
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "bipartite_strong_density");
    f.init();
    f.print_report(); // Write some informations in report.html

    let result = -f.optimal_value.expect("Failed to get optimal value");

    let bound = result / 24.;

    println!("Optimal bound: {:.4}Δ(G)⁴", bound);
}
