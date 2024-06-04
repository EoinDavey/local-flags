// Code to prove that if the square of the linegraph of a graph G with maximum degree Δ
// is a clique, then G has at most 5/4 Δ^2 edges

extern crate flag_algebra;
extern crate local_flags;

use flag_algebra::flags::{Connected, Graph};
use flag_algebra::*;
use local_flags::Degree;

type F = SubClass<Graph, Connected>;
type N = i64;
type V = QFlag<N, F>;

fn strong_degree() -> V {
    let edge: F = Graph::new(2, &[(0, 1)]).into();
    let t = Type::from_flag(&edge);
    Basis::new(4)
        .with_type(t)
        .qflag_from_indicator(|g: &F, _| g.content.edge(2, 3))
}

// Return true if the graph contains an induced 2K2
fn contains_a_2k2(g: &Graph) -> bool {
    for (u1, v1) in g.edges() {
        for (u2, v2) in g.edges() {
            if !g.edge(u1, u2) && !g.edge(u1, v2) && !g.edge(v1, u2) && !g.edge(v1, v2) {
                return true;
            }
        }
    }
    false
}

fn one(n: usize) -> V {
    let vertex: F = Graph::new(1, &[]).into();
    let t = Type::from_flag(&vertex);
    let edge = Degree::extension(t, 0); // Edge rooted on one side, its value of it is at most 1
    let mut result = edge.clone();
    for _ in 2..n {
        result = &result * &edge
    }
    result.untype()
}

// Sum of graphs containing a 2K2
fn flags_with_2k2(size: usize) -> V {
    Basis::new(size).qflag_from_indicator(|g: &F, _| contains_a_2k2(&g.content))
}

pub fn main() {
    init_default_log();

    let n = 6; // Maximal size of flags
    let basis = Basis::new(n);
    let edge: F = Graph::new(2, &[(0, 1)]).into();
    // We optimize the average strong degree,
    // which is also the total number of edges (minus 1) in a strong clique
    let obj = (strong_degree() * edge.project(n - 2)).untype();
    let mut ineqs = vec![flags_are_nonnegative(basis), flags_with_2k2(n).at_most(0)];

    ineqs.push(one(n).at_most(1));
    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<i64, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -obj,
    };

    let value = -pb
        .solve_csdp("strong_complete")
        .expect("Failed running csdp");
    println!("Maximal number of edges: {:?} times (Δ choose 2)", value);
}
