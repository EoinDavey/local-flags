extern crate flag_algebra;
extern crate local_flags;

use flag_algebra::flags::Graph;
use flag_algebra::*;
use local_flags::Degree;

pub enum ConnectedTriangleFree {}

impl SubFlag<Graph> for ConnectedTriangleFree {
    const SUBCLASS_NAME: &'static str = "Connected triangle-free graphs";

    const HEREDITARY: bool = false;

    fn is_in_subclass(flag: &Graph) -> bool {
        for i in 0..flag.size() {
            for j in 0..i {
                if flag.is_edge(i, j) {
                    for k in 0..j {
                        if flag.is_edge(j, k) && flag.is_edge(k, i) {
                            return false;
                        }
                    }
                }
            }
        }
        flag.is_connected()
    }
}

type F = SubClass<Graph, ConnectedTriangleFree>;
type V = QFlag<i64, F>;

fn rooted_vertex() -> V {
    flag_typed(&Graph::new(1, &[]).into(), 1)
}

fn rooted_c5() -> V {
    flag_typed(
        &Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]).into(),
        1,
    )
}

// Evaluates to 1 on every choice of root vertex
fn rooted_edge() -> V {
    flag_typed(&(Graph::new(2, &[(0, 1)])).into(), 1)
}

// n-vertex expression with one root that
// evaluates to 1 on every choice of root vertex.
// Equivalent to Degree::project(rooted_vertex, n-1) but
// expressed with simpler building blocks.
fn rooted_one(n: usize) -> V {
    let mut result = rooted_vertex();
    for _ in 1..n {
        result = result * rooted_edge()
    }
    result
}

// In this problem the value ("density") of a flag F
// represents the number of copies of F
// normalized by n * Δ^(|F| - 1) / |F|!.
pub fn main() {
    init_default_log();

    let n = 6; // Maximal size of flags
    let basis = Basis::new(n);

    // Number of C5s
    let obj = (rooted_c5() * rooted_one(n - 4)).untype();

    let mut ineqs = Degree::regularity(basis);
    ineqs.push(flags_are_nonnegative(basis));

    // Defines the density of an unlabelled vertex to be 1,
    // so that the "density" of any flag F
    // is #F / (Δ choose |F|) * Δ / #vertices.
    ineqs.push(rooted_one(n).untype().equal(1));

    let pb = Problem::<_, _> {
        ineqs,
        cs: basis.all_cs(),
        obj: -obj,
    };

    let value = -pb.solve_csdp("c5_free").expect("Failed running csdp");

    println!("Maximal number of C5: {value} times (Δ choose 5) * n / Δ");
    println!("that is {} times nΔ^4", value / 120.0);
    println!(
        "or {} times the presumed optimal nΔ^4/80",
        value / 120.0 * 80.0
    );
}
