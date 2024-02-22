/// Bound the local density of L(G)² for G bipartite and Δ regular.
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::{equal, iproduct, Itertools};
use local_flags::Degree;

type G = Colored<Graph, 4>;
#[derive(Debug, Clone, Copy)]
pub enum Bipartite4Connected {}
type F = SubClass<G, Bipartite4Connected>;

type N = f64;
type V = QFlag<N, F>;

impl SubFlag<G> for Bipartite4Connected {
    const SUBCLASS_NAME: &'static str = "Bipartite connected 4-coloured graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        // Each connected component contains a vertex colored 0 or 1
        if !flag.is_connected_to(|i| flag.color[i] <= 1) {
            return false;
        }
        for (u, v) in flag.content.edges() {
            if (flag.color[u] == 0 || flag.color[u] == 2)
                && (flag.color[v] == 0 || flag.color[v] == 2)
            {
                return false;
            }
            if (flag.color[u] == 1 || flag.color[u] == 3)
                && (flag.color[v] == 1 || flag.color[v] == 3)
            {
                return false;
            }
        }
        true
    }
}

fn connected_edges(g: &F, e1: &[usize; 2], e2: &[usize; 2]) -> bool {
    for &u1 in e1 {
        for &u2 in e2 {
            if g.content.content.edge(u1, u2) {
                return true;
            }
        }
    }
    false
}

// The three ways to split a 4-elements set into two parts of size 2
const SPLIT: [([usize; 2], [usize; 2]); 3] = [([0, 1], [2, 3]), ([0, 2], [1, 3]), ([0, 3], [1, 2])];

fn strong_density(basis: Basis<F>) -> V {
    basis.qflag_from_coeff(|g: &F, _| {
        let mut res = 0;
        for (e1, e2) in &SPLIT {
            if g.content.content.edge(e1[0], e1[1])
                && g.content.content.edge(e2[0], e2[1])
                && (e1.iter().any(|&v| g.content.color[v] <= 1))
                && (e2.iter().any(|&v| g.content.color[v] <= 1))
                && connected_edges(g, e1, e2)
            {
                res += 1
            }
        }
        res
    })
}

fn ones(n: usize, k: usize, col: u8) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![col; k]).into(), n)
}

pub fn main() {
    init_default_log();
    let n = 4;
    let basis = Basis::new(n);

    let mut ineqs = vec![
        flags_are_nonnegative(basis),
        ones(n, 1, 0).untype().at_most(1.),
        ones(n, 2, 0).untype().at_most(1.),
        ones(n, 3, 0).untype().at_most(1.),
        ones(n, 1, 1).untype().at_most(1.),
        ones(n, 2, 1).untype().at_most(1.),
        ones(n, 3, 1).untype().at_most(1.),
    ];

    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -strong_density(basis),
    }
    .no_scale();
    
    println!("CS Count: {}", pb.cs.len());

    let mut f = FlagSolver::new(pb, "bipartite_bruhn_joos");
    f.init();
    f.print_report(); // Write some informations in report.html

    let result = -f.optimal_value.expect("Failed to get optimal value");

    println!("Optimal value: {}", result); // Expect answer to be 24 = 4!.
}
