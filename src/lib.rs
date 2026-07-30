//! Curry-Howard in the Rust type system.
//!
//! | Logic          | This crate                                        |
//! |----------------|---------------------------------------------------|
//! | proposition    | [`Equal<L, R>`](gaussian::axioms::Equal) — a type |
//! | proof          | a type `P` with `P: ProofOf<Equal<L, R>>`         |
//! | proof checking | trait solving                                     |
//! | induction      | `impl<N: Gaussian> Gaussian for Successor<N>`     |
//!
//! The last row is the point: a recursive impl *is* the induction principle.
//! `rustc` checks the inductive step once, generically in `N`, which
//! establishes the theorem for every Peano natural at once.
//!
//! See [`gaussian`] for the worked example, Gauss's `n(n + 1) = T(n) + T(n)`.

// Proof terms nest one level per successor, so the trait solver needs headroom
// beyond the default 128. Must live at the crate root: `recursion_limit` is an
// inner attribute and has no effect inside a module.
#![recursion_limit = "512"]

pub mod gaussian;
