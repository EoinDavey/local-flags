use flag_algebra::flags::{CGraph, Colored, Graph};
use flag_algebra::*;
use ndarray::ScalarOperand;
use num::{FromPrimitive, Num, One, Zero};
use sprs::MulAcc;
use std::collections::BTreeSet;
use std::fmt::Display;
use std::marker::{Send, Sync};
use std::ops::{AddAssign, Neg};

// Returns a list of representative of the orbit classes
// of F under the action of its automorphism group
pub fn vertex_orbits<F: Flag>(flag: &F) -> Vec<usize> {
    let mut res = Vec::new();
    let mut orbits = BTreeSet::new();
    for i in 0..flag.size() {
        let unlabeled = flag.select_type(&[i]).canonical_typed(1);
        if orbits.insert(unlabeled) {
            res.push(i)
        }
    }
    res
}

/// A trait capturing the notion of degree of a graph
pub trait Degree: Flag {
    /// A weight function defining the degree
    ///
    /// The degree of u is the sum of weight(u, v) over every other v
    fn is_edge(&self, u: usize, v: usize) -> bool;

    /// Weighted sum of flags extending t on vertex i
    fn extension<N: One + Zero>(t: Type<Self>, i: usize) -> QFlag<N, Self> {
        assert!(i < t.size);
        assert!(t.size <= 12);
        let b = Basis::new(t.size + 1).with_type(t);
        b.qflag_from_indicator(move |flag, type_size| flag.is_edge(i, type_size))
            .named(format!("ext({{{}}}, {})", t.print_concise(), i))
    }

    //
    fn project<N: One + Zero>(&self, n: usize) -> QFlag<N, Self> {
        let k = self.size();
        assert!(k <= n);
        assert!(0 < k);
        let t = Type::from_flag(self);
        let basis = Basis::new(n).with_type(t);
        basis.qflag_from_coeff(move |g: &Self, s| {
            assert_eq!(s, k);
            if (k..n).all(|i| g.is_edge(0, i)) {
                N::one()
            } else {
                N::zero()
            }
        })
    }

    /// Equalities true if every vertex has same degree
    fn regularity<N>(basis: Basis<Self>) -> Vec<Ineq<N, Self>>
    where
        N: Clone + Num + FromPrimitive + Display + AddAssign + ScalarOperand,
    {
        assert_eq!(basis.t, Type::empty());
        let type_size = basis.size - 1;
        let flags_type = Basis::<Self>::new(type_size).get();
        let mut res = Vec::new();
        for (id, flag) in flags_type.iter().enumerate() {
            let orbits = vertex_orbits(flag);
            if orbits.len() >= 2 {
                let t = Type::new(type_size, id);
                for i in 0..orbits.len() {
                    let next_i = (i + 1) % orbits.len();
                    let v = (Degree::extension(t, orbits[i])
                        - Degree::extension(t, orbits[next_i]))
                    .untype();
                    res.push(v.non_negative());
                }
            }
        }
        res
    }
    fn weaker_regularity<N>(basis: Basis<Self>, type_size: usize) -> Vec<Ineq<N, Self>>
    where
        N: Num
            + Clone
            + Send
            + Sync
            + Default
            + FromPrimitive
            + AddAssign
            + std::iter::Sum
            + MulAcc
            + Neg<Output = N>
            + ndarray::ScalarOperand
            + Display,
    {
        assert_eq!(basis.t, Type::empty());
        assert!(type_size >= 1);
        assert!(type_size < basis.size);
        let flags_type = Basis::<Self>::new(type_size).get();
        let mut res = Vec::new();
        for (id, flag) in flags_type.iter().enumerate() {
            let orbits = vertex_orbits(flag);
            if orbits.len() >= 2 {
                let t = Type::new(type_size, id);
                for i in 0..orbits.len() {
                    let next_i = (i + 1) % orbits.len();
                    let v = Degree::extension(t, orbits[i]) - Degree::extension(t, orbits[next_i]);
                    res.push(v.non_negative().multiply_and_unlabel(basis));
                }
            }
        }
        res
    }
    fn is_connected_to<F>(&self, f: F) -> bool
    where
        F: Fn(usize) -> bool,
    {
        if self.size() == 0 {
            return true;
        };
        let mut visited = vec![false; self.size()];
        let mut stack = Vec::new();
        for u in 0..self.size() {
            if f(u) {
                stack.push(u)
            }
        }
        while let Some(v) = stack.pop() {
            if !visited[v] {
                visited[v] = true;
                for u in 0..self.size() {
                    if u != v && self.is_edge(u, v) {
                        stack.push(u)
                    }
                }
            }
        }
        visited.into_iter().all(|b| b)
    }

    fn is_connected(&self) -> bool {
        self.is_connected_to(|i| i == 0)
    }
}

// Implementations for classes of flags
impl Degree for Graph {
    fn is_edge(&self, u: usize, v: usize) -> bool {
        self.edge(u, v)
    }
}

impl<const C: u8> Degree for CGraph<C>
where
    CGraph<C>: Flag,
{
    fn is_edge(&self, u: usize, v: usize) -> bool {
        CGraph::is_edge(self, u, v)
    }
}

// Heredity implementation for derived classes
impl<F, A> Degree for SubClass<F, A>
where
    F: Degree,
    A: SubFlag<F>,
{
    fn is_edge(&self, u: usize, v: usize) -> bool {
        self.content.is_edge(u, v)
    }
}

impl<F, const C: u8> Degree for Colored<F, C>
where
    F: Degree,
    Colored<F, C>: Flag,
{
    fn is_edge(&self, u: usize, v: usize) -> bool {
        self.content.is_edge(u, v)
    }
}
