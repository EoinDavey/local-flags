/// Bound the number of copies of C5 containing any particular
/// vertex in a triangle free Δ regular graph.
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::{equal, Itertools, iproduct};
use local_flags::Degree;

type G = Colored<Graph, 2>;
#[derive(Debug, Clone, Copy)]
pub enum TriangleFreeConnected {}
type F = SubClass<G, TriangleFreeConnected>;

type N = f64;
type V = QFlag<N, F>;

impl SubFlag<G> for TriangleFreeConnected {
    const SUBCLASS_NAME: &'static str = "Triangle Free Connected 2-colored graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        // Each connected component contains a vertex colored 0
        if !flag.is_connected_to(|i| flag.color[i] == 0) {
            return false;
        }
        for (u, v) in flag.content.edges() {
            if flag.color[u] == 0 && flag.color[v] == 0 {
                return false;
            }
        }
        let n = flag.content.size();
        for (u, v, w) in iproduct!(0..n, 0..n, 0..n) {
            if u == v || u == w || v == w {
                continue
            }
            if !flag.content.edge(u, v) || !flag.content.edge(u, w) || !flag.content.edge(v, w) {
                continue
            }
            return false
        }
        true
    }
}

fn ones(n: usize, k: usize) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![0; k]).into(), n)
}

pub fn main() {
    init_default_log();
    let n = 6;
    let basis = Basis::new(n);

    let c5_path: F = Colored::new(Graph::new(4, &[(0, 1), (1, 2), (2, 3)]), vec![0, 1, 1, 0]).into();
    let new_obj = Degree::project(&c5_path, n).untype();

    let mut ineqs = vec![
        flags_are_nonnegative(basis),
    ];
    for i in 1..n {
        ineqs.push(ones(n, i).untype().equal(1.))
    }

    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -new_obj,
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "bounded_pentagon");
    f.init();
    f.print_report(); // Write some informations in report.html

    let result = -f.optimal_value.expect("Failed to get optimal value");

    println!("Optimal value: {}", result);
}
