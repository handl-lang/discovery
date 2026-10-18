//! Enumeration determinism + cap tests — the Python contract on
//! small fixtures (`oracle._diag_product`, `_diag_groups`,
//! `_binding_envs`, `escalate_limit`).

use handl_discovery::{
    GUARDED_CAP, LazySeq, MAX_BINDING_ENVS, binding_envs, binding_envs_capped, combos_at_sum,
    diag_groups, diag_product, escalate_limit,
};

/// Cantor order over a product: index-sum batches, head coordinate
/// outermost — `oracle._diag_product` verbatim.
#[test]
fn diag_product_cantor_order() {
    let got: Vec<Vec<i32>> = diag_product(vec![vec![0, 1, 2], vec![10, 20]]).collect();
    // (i,j) index-sum order: 0 -> (0,0); 1 -> (0,1),(1,0);
    // 2 -> (1,1),(2,0); 3 -> (2,1).
    assert_eq!(
        got,
        vec![
            vec![0, 10],
            vec![0, 20],
            vec![1, 10],
            vec![1, 20],
            vec![2, 10],
            vec![2, 20],
        ]
    );
}

/// `combos_at_sum` yields exactly the index-sum == total slice.
#[test]
fn combos_at_sum_exact_slice() {
    let lists = vec![vec!['a', 'b'], vec!['x', 'y', 'z'], vec!['p', 'q']];
    let got: Vec<Vec<char>> =
        combos_at_sum(&[vec!['a', 'b'], vec!['x', 'y'], vec!['p', 'q']], 1).collect();
    // total=1: (0,0,1),(0,1,0),(1,0,0) in scan order.
    assert_eq!(
        got,
        vec![
            vec!['a', 'x', 'q'],
            vec!['a', 'y', 'p'],
            vec!['b', 'x', 'p'],
        ]
    );
    // total above max index-sum yields nothing.
    assert!(combos_at_sum(&lists, 99).next().is_none());
    // an empty list empties the product.
    assert!(diag_product::<i32>(vec![vec![1], vec![]]).next().is_none());
    // no lists: only total 0 yields the empty tuple.
    let empty: Vec<Vec<i32>> = Vec::new();
    assert_eq!(
        combos_at_sum(&empty, 0).collect::<Vec<_>>(),
        vec![Vec::<i32>::new()]
    );
    assert!(combos_at_sum(&empty, 1).next().is_none());
}

/// A cap truncates a corner, not a dimension — the fairness claim:
/// the tail of coordinate 0 is reached before coordinate 1's deep
/// tail, so a short prefix covers every coordinate's low indices.
#[test]
fn diag_product_cap_covers_corner() {
    // itertools.product order would reach (9, x) only after all of
    // coordinate 0 — diagonal reaches it at index ~11.
    let first: Vec<Vec<i32>> = diag_product(vec![vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], vec![0, 1]])
        .take(6)
        .collect();
    assert!(first.contains(&vec![2, 0])); // corner coverage
    assert!(!first.contains(&vec![9, 0])); // whole-dimension exhaustion avoided
}

/// `diag_groups` interleaves ragged groups by `v + a`.
#[test]
fn diag_groups_ragged_order() {
    let groups = vec![
        LazySeq::from_vec(vec!["g0a", "g0b"]),
        LazySeq::from_vec(vec!["g1a"]),
        LazySeq::from_vec(vec!["g2a", "g2b", "g2c"]),
    ];
    let got: Vec<&str> = diag_groups(groups).collect();
    // total 0: g0[0]; total 1: g1[0], g0[1]; total 2: g2[0];
    // total 3: g2[1]; total 4: g2[2].
    assert_eq!(got, vec!["g0a", "g1a", "g0b", "g2a", "g2b", "g2c"]);
}

/// `diag_groups` over lazy sources probes only the prefix it needs.
#[test]
fn diag_groups_lazy_probe() {
    use std::cell::Cell;
    use std::rc::Rc;
    let pulled = Rc::new(Cell::new(0usize));
    let g0 = LazySeq::new(
        std::iter::from_fn({
            let pulled = pulled.clone();
            move || {
                pulled.set(pulled.get() + 1);
                Some(pulled.get())
            }
        })
        .take(3),
    );
    let g1 = LazySeq::from_vec(vec![100usize, 200, 300]);
    let mut it = diag_groups(vec![g0, g1]);
    let first = it.next().unwrap();
    assert_eq!(first, 1);
    // g0[0] needed only one pull of the lazy source.
    assert_eq!(pulled.get(), 1);
    let rest: Vec<usize> = it.collect();
    assert_eq!(rest, vec![100, 2, 200, 3, 300]);
}

/// `binding_envs`: the `(base, combo)` diagonal, lazily pulled —
/// the spec's exact round trace on a three-base fixture.
#[test]
fn binding_envs_cantor_order() {
    let bases = vec![
        ("b0", vec!["c00", "c01", "c02"].into_iter()),
        ("b1", vec!["c10", "c11"].into_iter()),
        ("b2", vec!["c20"].into_iter()),
    ];
    let got: Vec<(&str, &str)> = binding_envs(bases.into_iter()).collect();
    // round 0: (b0,c00). round 1: (b1,c10),(b0,c01).
    // round 2: (b2,c20),(b1,c11),(b0,c02). entries then die in
    // descending-i scan order, invisibly.
    assert_eq!(
        got,
        vec![
            ("b0", "c00"),
            ("b1", "c10"),
            ("b0", "c01"),
            ("b2", "c20"),
            ("b1", "c11"),
            ("b0", "c02"),
        ]
    );
}

/// A base whose combo stream is empty lands then dies on its first
/// pull — it neither stalls nor shifts later bases' order.
#[test]
fn binding_envs_empty_base() {
    let bases = vec![
        ("b0", Vec::<&str>::new().into_iter()),
        ("b1", vec!["c10"].into_iter()),
    ];
    let got: Vec<(&str, &str)> = binding_envs(bases.into_iter()).collect();
    assert_eq!(got, vec![("b1", "c10")]);
}

/// The env cap is a work bound: a capped sweep yields exactly `cap`
/// pairs and stops, even with space remaining.
#[test]
fn binding_envs_cap() {
    // Infinite bases of infinite combos — only the cap terminates it.
    let src = (0..).map(|b| {
        (
            b,
            Box::new(std::iter::repeat_n(b, 4)) as Box<dyn Iterator<Item = usize>>,
        )
    });
    let got: Vec<(usize, usize)> = binding_envs_capped(src, 7).collect();
    assert_eq!(got.len(), 7);
    // Cantor prefix: (0,c0),(1,c0),(0,c1),(2,c0),(1,c1),(0,c2),(3,c0)
    assert_eq!(
        got.iter().map(|(b, c)| (*b, *c)).collect::<Vec<_>>(),
        vec![(0, 0), (1, 1), (0, 0), (2, 2), (1, 1), (0, 0), (3, 3)]
    );
}

/// The default cap is the spec's 250k — a sweep smaller than that
/// runs to natural exhaustion; the constant itself is the contract.
#[test]
fn binding_envs_default_cap_is_specs() {
    assert_eq!(MAX_BINDING_ENVS, 250_000);
    assert_eq!(GUARDED_CAP, 2000);
}

/// `escalate_limit` — the selective-cap truth table.
#[test]
fn escalate_limit_policy() {
    // starved guarded sweep escalates once.
    assert_eq!(escalate_limit(360, true, 0), GUARDED_CAP);
    // unguarded never escalates.
    assert_eq!(escalate_limit(360, false, 0), 360);
    // an accepted window never escalates.
    assert_eq!(escalate_limit(360, true, 3), 360);
    // never below the passed limit.
    assert_eq!(escalate_limit(5000, true, 0), 5000);
}
