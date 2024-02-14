/// Bound the number of copies of C5 containing any particular
/// vertex in a Δ regular graph.
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

fn obj(n: usize) -> V {
    Basis::new(n).qflag_from_coeff(move |g: &F, _| {
        let mut res = 0;
        for perm in (0..n).permutations(4) {
            let cols: Vec<u8> = perm.iter().map(|i| g.content.color[*i]).collect();
            if !equal(cols, vec![0, 1, 1, 0]) {
                continue;
            }
            if !(g.content.content.edge(perm[0], perm[1])
                && g.content.content.edge(perm[1], perm[2])
                && g.content.content.edge(perm[2], perm[3]))
            {
                continue;
            }
            res += 1
        }
        assert!(res % 2 == 0);
        res / 2
    })
}

fn ones(n: usize, k: usize) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![0; k]).into(), n)
}

pub fn main() {
    init_default_log();
    let n = 5;
    let basis = Basis::new(n);

    let mut ineqs = vec![
        flags_are_nonnegative(basis),
        ones(n, 1).untype().at_most(1.),
        ones(n, 2).untype().at_most(1.),
        ones(n, 3).untype().at_most(1.),
    ];

    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -obj(n),
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "bounded_pentagon");
    f.init();
    f.print_report(); // Write some informations in report.html

    let result = -f.optimal_value.expect("Failed to get optimal value");

    println!("Optimal value: {}", result); // Expect answer to be 24 = 4!.
}
