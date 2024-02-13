/// Bound the number of copies of C5 containing any particular
/// vertex in a Δ regular graph.
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::{equal, Itertools};
use local_flags::Degree;

type G = Colored<Graph, 2>;
#[derive(Debug, Clone, Copy)]
pub enum Connected {}
type F = SubClass<G, Connected>;

type N = f64;
type V = QFlag<N, F>;

impl SubFlag<G> for Connected {
    const SUBCLASS_NAME: &'static str = "Connected 2-colored graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &G) -> bool {
        // Each connected component contains a vertex colored 0
        flag.is_connected_to(|i| flag.color[i] == 0)
    }
}

fn obj() -> V {
    Basis::new(4).qflag_from_coeff(|g: &F, _| {
        let mut res = 0;
        for perm in (0..4).permutations(4) {
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
        res
    })
}

fn ones(n: usize, k: usize) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![0; k]).into(), n)
}

pub fn main() {
    init_default_log();
    let basis = Basis::new(4);

    let mut ineqs = vec![
        flags_are_nonnegative(basis),
        ones(4, 1).untype().at_most(1.),
        ones(4, 2).untype().at_most(1.),
        ones(4, 3).untype().at_most(1.),
    ];

    ineqs.append(&mut Degree::regularity(basis));

    let pb = Problem::<N, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -obj(),
    }
    .no_scale();

    let mut f = FlagSolver::new(pb, "regular_c5_bound");
    f.init();
    f.print_report(); // Write some informations in report.html

    let result = -f.optimal_value.expect("Failed to get optimal value");

    println!("Optimal value: {}", result); // Expect answer to be 24 = 4!.
}
