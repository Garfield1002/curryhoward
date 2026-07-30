# curryhoward

`n(n + 1) = T(n) + T(n)` for every natural `n`,
proved by the Rust trait solver, with no runtime code and no values ever constructed.
This is called Gauss Theorem here just to make us feel good about ourselves.

[`article.md`](article.md) is the write-up: how it works, what it costs, and what the same proof looks like in Lean.

```
cargo test                                        # 11 tests, 3 of which must fail to compile
cargo doc --open
elan run leanprover/lean4:v4.31.0 lean gauss.lean # the Lean mirror, no Mathlib needed
```

## Layout

```
src/lib.rs       crate root, recursion_limit
src/gaussian.rs  axioms (trusted) / arithmetic lemmas / Gauss / examples
gauss.lean       the same proof in Lean: 49 lines, zero axioms
article.md       the write-up
```

Start at `gaussian::examples`.
It is staged by how much work each proof needs: concrete arithmetic that is free, one-law rewrites, two-step compositions, then reuse of the main theorem.

## The trusted base

`ProofOf` is sealed, so only `gaussian::axioms` can implement it and no
downstream crate can assert a new axiom to prove `0 = 1` — there is a
`compile_fail` doctest pinning that. The base is four rules, and the list cannot
silently fall out of date, because `ProofOf` requires the `Axiom` marker as a
supertrait:

```
grep 'Axiom for' src/gaussian.rs
```
