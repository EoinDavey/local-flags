/// Bound the number of copies of C5 containing any particular
/// vertex in a triangle free Δ regular graph.
use flag_algebra::flags::{Colored, Graph};
use flag_algebra::*;
use itertools::{equal, Itertools, iproduct};
use local_flags::Degree;

use num::pow::Pow;

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
        /*
        for (u, v, w, a, b) in iproduct!(0..n, 0..n, 0..n, 0..n, 0..n) {
            if v == u || w == u || w == v || a ==u || a == v || a == w || b == u || b== v || b ==w || b == a {
                continue
            }
            if !flag.content.edge(u, v) || !flag.content.edge(v, w) || !flag.content.edge(w, a)
                || !flag.content.edge(a, b) || !flag.content.edge(b, u) {
                continue
            }
            let mut cnt = 0;
            if flag.color[u] == 0 {
                cnt+=1;
            }
            if flag.color[v] == 0 {
                cnt+=1;
            }
            if flag.color[w] == 0 {
                cnt+=1;
            }
            if flag.color[a] == 0 {
                cnt+=1;
            }
            if flag.color[b] == 0 {
                cnt+=1;
            }
            if cnt == 1 {
                return false;
            }
        }*/
        true
    }
}

// Sum of flags with type `t` and size `t.size + 1` where the extra vertex is in X
fn extension_in_x(t: Type<F>) -> V {
    let b = Basis::new(t.size + 1).with_type(t);
    b.qflag_from_indicator(|g: &F, type_size| g.content.color[type_size] == 0)
        .named(format!("ext_in_x({{{}}})", t.print_concise()))
}

// Equalities expressing that extensions in X have twice the weight of extensions through an edge
fn size_of_x(n: usize) -> Vec<Ineq<N, F>> {
    let mut res = Vec::new();
    for t in Type::types_with_size(n - 1) {
        let diff = Degree::extension(t, 0) - extension_in_x(t);
        res.push(diff.equal(0.).untype());
    }
    res
}

fn ones(n: usize, k: usize) -> V {
    Degree::project(&Colored::new(Graph::empty(k), vec![0; k]).into(), n)
}

fn obj(n: usize) -> V {
    let c5_one_black: F = Colored::new(Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), vec![0, 1, 1, 1, 1]).into();
    let c5_two_black: F = Colored::new(Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), vec![0, 1, 0, 1, 1]).into();

    Degree::project(&c5_one_black, n).untype() + Degree::project(&c5_two_black, n).untype() * 2.0
}

pub fn main() {
    init_default_log();
    let n = 6;
    let basis = Basis::new(n);

    // let c5_path: F = Colored::new(Graph::new(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]), vec![0, 1, 0, 1, 1]).into();
    // let new_obj = Degree::project(&c5_path, n).untype();

    let mut ineqs = vec![
        flags_are_nonnegative(basis),
    ];
    for i in 1..=n {
        ineqs.push(ones(n, i).untype().equal(1.));
    }

    ineqs.append(&mut Degree::regularity(basis));
    ineqs.append(&mut size_of_x(n));

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

    println!("Optimal value: {}", result);
}
