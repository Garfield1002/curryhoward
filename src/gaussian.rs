//! Gauss's theorem, `n(n + 1) = T(n) + T(n)`, proved for every Peano natural
//! by the Rust trait solver.
//!
//! The file is split into two regions:
//!
//! - [`axioms`] holds the **trusted base**: inference rules asserted, not
//!   derived. `ProofOf` is sealed, so no impl outside that module can add one.
//! - Everything below it is **derived**: composite proof terms that `rustc`
//!   checks against the rules in the trusted base.
//!
//! Proof terms are types, never values, so nothing here is ever constructed.

#![allow(dead_code)]
// Bounds on type-alias parameters are not enforced by rustc, but they document
// what each proof term expects. The real check happens where the alias is used
// to satisfy an associated-type bound.
#![allow(type_alias_bounds)]

use std::marker::PhantomData;

// ============================================================================
// AXIOMS — trusted, unproven
// ============================================================================

/// The trusted base of the proof system.
///
/// These rules cannot be derived. `ProofOf` is a shallow embedding: a
/// proposition is an uninhabited marker type and a proof is a type asserted to
/// satisfy `ProofOf<_>`. There is no elimination principle (no `J`/`subst`),
/// so nothing can case-split on a proof and rewrite with it — and Rust cannot
/// express one, since it would need to compute a type *from* a proof.
///
/// Soundness is argued by hand, under the reading:
///
/// > `P: ProofOf<Equal<L, R>>` holds only when `L` and `R` are the same type.
///
/// Each impl below preserves that reading, so the system has a model and is
/// therefore consistent.
pub mod axioms {
    use super::{Number, TypeFn};
    use std::marker::PhantomData;

    mod private {
        pub trait Sealed {}
    }

    /// Marker for every rule taken on trust. `grep 'for .* Axiom'` lists the
    /// entire trusted base, and the list cannot silently fall out of date:
    /// [`ProofOf`] requires it, so a rule that is not declared an `Axiom`
    /// cannot prove anything. `Axiom` is itself sealed, so the base cannot be
    /// extended from outside this module.
    pub trait Axiom: private::Sealed {}

    /// `P: ProofOf<Prop>` — `P` is a proof of `Prop`.
    ///
    /// The `Axiom` supertrait is the enforcement: every proof term in the
    /// system is one of the four rules below, or a composition of them.
    pub trait ProofOf<Proposition>: Axiom {}

    /// The proposition `L = R`.
    pub struct Equal<L, R>(PhantomData<(L, R)>);

    // ---- Reflexivity: ⊢ T = T ----
    pub struct Refl<T>(PhantomData<T>);
    impl<T> private::Sealed for Refl<T> {}
    impl<T> Axiom for Refl<T> {}
    impl<T> ProofOf<Equal<T, T>> for Refl<T> {}

    // ---- Symmetry: L = R ⊢ R = L ----
    pub struct Sym<P>(PhantomData<P>);
    impl<P> private::Sealed for Sym<P> {}
    impl<P> Axiom for Sym<P> {}
    impl<L, R, P> ProofOf<Equal<R, L>> for Sym<P> where P: ProofOf<Equal<L, R>> {}

    // ---- Transitivity: L = M, M = R ⊢ L = R ----
    //
    // `Middle` has to be written out at every use, which is the single biggest
    // ergonomic tax in this file — a long chain of rewrites means spelling out
    // every intermediate term (see `GaussM1`..`GaussM4`).
    //
    // It is not laziness in the encoding. `Middle` appears in both premises but
    // in neither the conclusion nor the self type, so the solver has nothing to
    // infer it from; leaving it off is the E0207 error. Real proof
    // assistants avoid this with unification and elaboration during proof
    // search, machinery the trait solver deliberately does not have.
    pub struct Trans<P, Q, Middle>(PhantomData<(P, Q, Middle)>);
    impl<P, Q, M> private::Sealed for Trans<P, Q, M> {}
    impl<P, Q, M> Axiom for Trans<P, Q, M> {}
    impl<L, Middle, R, P, Q> ProofOf<Equal<L, R>> for Trans<P, Q, Middle>
    where
        P: ProofOf<Equal<L, Middle>>,
        Q: ProofOf<Equal<Middle, R>>,
    {
    }

    // ---- Leibniz congruence: A = B ⊢ F(A) = F(B) ----
    //
    // This single rule subsumes what would otherwise be one axiom per
    // operation (successor, add-left, add-right, multiply-left, ...). Each
    // additional congruence now costs only a `TypeFn` impl, which is pure
    // computation and carries no trust.
    //
    // `A` and `B` are struct parameters rather than where-clause-only
    // parameters: a type parameter appearing solely in a predicate is not a
    // constraining position, and rustc rejects such an impl with E0207.
    pub struct Cong<F, A, B, P>(PhantomData<(F, A, B, P)>);
    impl<F, A, B, P> private::Sealed for Cong<F, A, B, P> {}
    impl<F, A, B, P> Axiom for Cong<F, A, B, P> {}
    impl<F, A, B, P> ProofOf<Equal<F::Apply<A>, F::Apply<B>>> for Cong<F, A, B, P>
    where
        F: TypeFn,
        A: Number,
        B: Number,
        P: ProofOf<Equal<A, B>>,
    {
    }
}

pub use axioms::{Cong, Equal, ProofOf, Refl, Sym, Trans};

// ============================================================================
// DERIVED — machine-checked from the axioms above
// ============================================================================

// ---------- Peano naturals and arithmetic ----------

pub struct Zero;
pub struct Successor<N>(PhantomData<N>);

pub type One = Successor<Zero>;
pub type Two = Successor<One>;
pub type Three = Successor<Two>;
pub type Four = Successor<Three>;
pub type Five = Successor<Four>;
pub type Six = Successor<Five>;
pub type Seven = Successor<Six>;
pub type Eight = Successor<Seven>;
pub type Nine = Successor<Eight>;
pub type Ten = Successor<Nine>;

pub trait Arithmetic: Sized {
    type Add<Rhs: Number>: Number;
    type Mul<Rhs: Number>: Number;
    type Triangle: Number;
}

pub type Sum<L, R> = <L as Arithmetic>::Add<R>;
pub type Product<L, R> = <L as Arithmetic>::Mul<R>;
pub type Triangle<N> = <N as Arithmetic>::Triangle;
pub type Double<N> = Sum<N, N>;

/// A number carries not just operations, but witnesses for the laws needed
/// later. Each associated type is a *proof obligation*: the bound is checked
/// at every impl.
pub trait Number: Arithmetic + Sized {
    type AddZero: ProofOf<Equal<Sum<Self, Zero>, Self>>;

    type AddSucc<R: Number>: ProofOf<Equal<Sum<Self, Successor<R>>, Successor<Sum<Self, R>>>>;

    type AddAssoc<B: Number, C: Number>: ProofOf<Equal<Sum<Sum<Self, B>, C>, Sum<Self, Sum<B, C>>>>;

    type AddComm<R: Number>: ProofOf<Equal<Sum<Self, R>, Sum<R, Self>>>;

    type MulSucc<R: Number>: ProofOf<
        Equal<Product<Self, Successor<R>>, Sum<Self, Product<Self, R>>>,
    >;
}

impl Arithmetic for Zero {
    type Add<Rhs: Number> = Rhs;
    type Mul<Rhs: Number> = Zero;
    type Triangle = Zero;
}

impl<N: Number> Arithmetic for Successor<N> {
    type Add<Rhs: Number> = Successor<Sum<N, Rhs>>;
    type Mul<Rhs: Number> = Sum<Rhs, Product<N, Rhs>>;
    type Triangle = Sum<Self, Triangle<N>>;
}

// ---------- Type-level functions, for congruence ----------
//
// Pure computation: a `TypeFn` impl adds nothing to the trusted base. It only
// names a context into which `Cong` may rewrite.

/// A function on numbers, at the type level.
pub trait TypeFn {
    type Apply<X: Number>: Number;
}

pub struct SuccFn;
impl TypeFn for SuccFn {
    type Apply<X: Number> = Successor<X>;
}

pub struct AddLeftFn<L>(PhantomData<L>);
impl<L: Number> TypeFn for AddLeftFn<L> {
    type Apply<X: Number> = Sum<L, X>;
}

pub struct AddRightFn<R>(PhantomData<R>);
impl<R: Number> TypeFn for AddRightFn<R> {
    type Apply<X: Number> = Sum<X, R>;
}

pub struct MulLeftFn<L>(PhantomData<L>);
impl<L: Number> TypeFn for MulLeftFn<L> {
    type Apply<X: Number> = Product<L, X>;
}

// Derived congruence rules. Each is an instance of the single `Cong` axiom.

/// `A = B ⊢ A + 1 = B + 1`
pub type SuccCong<A: Number, B: Number, P> = Cong<SuccFn, A, B, P>;

/// `A = B ⊢ L + A = L + B`
pub type AddCongLeft<L: Number, A: Number, B: Number, P> = Cong<AddLeftFn<L>, A, B, P>;

/// `A = B ⊢ A + R = B + R`
pub type AddCongRight<A: Number, B: Number, R: Number, P> = Cong<AddRightFn<R>, A, B, P>;

/// `A = B ⊢ L * A = L * B`
pub type MulCongLeft<L: Number, A: Number, B: Number, P> = Cong<MulLeftFn<L>, A, B, P>;

// ---------- Derived rearrangement lemmas ----------

/// `A + (B + C) = B + (A + C)`
pub type SwapFront<A: Number, B: Number, C: Number> = Trans<
    Sym<<A as Number>::AddAssoc<B, C>>,
    Trans<
        AddCongRight<Sum<A, B>, Sum<B, A>, C, <A as Number>::AddComm<B>>,
        <B as Number>::AddAssoc<A, C>,
        Sum<Sum<B, A>, C>,
    >,
    Sum<Sum<A, B>, C>,
>;

/// `(A + B) + (C + D) = (A + C) + (B + D)`
pub type Shuffle<A: Number, B: Number, C: Number, D: Number> = Trans<
    <A as Number>::AddAssoc<B, Sum<C, D>>,
    Trans<
        AddCongLeft<A, Sum<B, Sum<C, D>>, Sum<C, Sum<B, D>>, SwapFront<B, C, D>>,
        Sym<<A as Number>::AddAssoc<C, Sum<B, D>>>,
        Sum<A, Sum<C, Sum<B, D>>>,
    >,
    Sum<A, Sum<B, Sum<C, D>>>,
>;

/// `(N + 2) + N = (N + 1) + (N + 1)`
pub type SuccPair<N: Number> =
    SuccCong<Successor<Sum<N, N>>, Sum<N, Successor<N>>, Sym<<N as Number>::AddSucc<N>>>;

// ---------- The arithmetic laws, by induction ----------

impl Number for Zero {
    type AddZero = Refl<Zero>;
    type AddSucc<R: Number> = Refl<Successor<R>>;
    type AddAssoc<B: Number, C: Number> = Refl<Sum<B, C>>;
    type AddComm<R: Number> = Sym<<R as Number>::AddZero>;
    type MulSucc<R: Number> = Refl<Zero>;
}

impl<N: Number> Number for Successor<N> {
    type AddZero = SuccCong<Sum<N, Zero>, N, <N as Number>::AddZero>;

    type AddSucc<R: Number> =
        SuccCong<Sum<N, Successor<R>>, Successor<Sum<N, R>>, <N as Number>::AddSucc<R>>;

    type AddAssoc<B: Number, C: Number> =
        SuccCong<Sum<Sum<N, B>, C>, Sum<N, Sum<B, C>>, <N as Number>::AddAssoc<B, C>>;

    type AddComm<R: Number> = Trans<
        SuccCong<Sum<N, R>, Sum<R, N>, <N as Number>::AddComm<R>>,
        Sym<<R as Number>::AddSucc<N>>,
        Successor<Sum<R, N>>,
    >;

    type MulSucc<R: Number> = Trans<
        AddCongLeft<
            Successor<R>,
            Product<N, Successor<R>>,
            Sum<N, Product<N, R>>,
            <N as Number>::MulSucc<R>,
        >,
        SuccCong<
            Sum<R, Sum<N, Product<N, R>>>,
            Sum<N, Sum<R, Product<N, R>>>,
            SwapFront<R, N, Product<N, R>>,
        >,
        Sum<Successor<R>, Sum<N, Product<N, R>>>,
    >;
}

// ---------- Gauss's theorem ----------

/// Core theorem: `n(n + 1) = T(n) + T(n)`.
pub trait Gaussian: Number {
    type Proof: ProofOf<Equal<Product<Self, Successor<Self>>, Double<Triangle<Self>>>>;
}

impl Gaussian for Zero {
    type Proof = Refl<Zero>;
}

// Intermediate terms of the inductive step, for `N + 1`:
//
//   (N+1)(N+2)
// = (N+2) + N(N+2)          [definition of *]
// = (N+2) + (N + N(N+1))    GaussStep1, by MulSucc
// = (N+2) + (N + 2T(N))     GaussStep2, by the induction hypothesis
// = ((N+2) + N) + 2T(N)     GaussStep3, by associativity
// = ((N+1) + (N+1)) + 2T(N) GaussStep4, by SuccPair
// = ((N+1) + T(N)) + ((N+1) + T(N))
//                           GaussStep5, by Shuffle
// = 2T(N+1)                 [definition of Triangle]

type GaussM1<N: Number> = Sum<Successor<Successor<N>>, Sum<N, Product<N, Successor<N>>>>;
type GaussM2<N: Number> = Sum<Successor<Successor<N>>, Sum<N, Double<Triangle<N>>>>;
type GaussM3<N: Number> = Sum<Sum<Successor<Successor<N>>, N>, Double<Triangle<N>>>;
type GaussM4<N: Number> = Sum<Sum<Successor<N>, Successor<N>>, Double<Triangle<N>>>;

type GaussStep1<N: Number> = AddCongLeft<
    Successor<Successor<N>>,
    Product<N, Successor<Successor<N>>>,
    Sum<N, Product<N, Successor<N>>>,
    <N as Number>::MulSucc<Successor<N>>,
>;

type GaussStep2<N: Gaussian> = AddCongLeft<
    Successor<Successor<N>>,
    Sum<N, Product<N, Successor<N>>>,
    Sum<N, Double<Triangle<N>>>,
    AddCongLeft<N, Product<N, Successor<N>>, Double<Triangle<N>>, <N as Gaussian>::Proof>,
>;

type GaussStep3<N: Number> =
    Sym<<Successor<Successor<N>> as Number>::AddAssoc<N, Double<Triangle<N>>>>;

type GaussStep4<N: Number> = AddCongRight<
    Sum<Successor<Successor<N>>, N>,
    Sum<Successor<N>, Successor<N>>,
    Double<Triangle<N>>,
    SuccPair<N>,
>;

type GaussStep5<N: Number> = Shuffle<Successor<N>, Successor<N>, Triangle<N>, Triangle<N>>;

type GaussStep<N: Gaussian> = Trans<
    GaussStep1<N>,
    Trans<
        GaussStep2<N>,
        Trans<GaussStep3<N>, Trans<GaussStep4<N>, GaussStep5<N>, GaussM4<N>>, GaussM3<N>>,
        GaussM2<N>,
    >,
    GaussM1<N>,
>;

impl<N: Gaussian> Gaussian for Successor<N> {
    type Proof = GaussStep<N>;
}

// ---------- Checks ----------
//
// A note on reading failures. When a proof is wrong, the error is a wall of
// fully-normalized associated types — `<<R as Arithmetic>::Add<N> as
// Arithmetic>::Add<<N as Arithmetic>::Mul<R>>` rather than `(R + N) + N*R` —
// and rustc will often spill the full type to a `long-type-*.txt` file. Worse,
// the blame usually lands on the outermost `Trans`, not on the step that
// actually went wrong, because the solver fails at the point where the chain
// stops lining up.
//
// The practical technique is bisection: pull a suspect sub-proof out and pin it
// with `check::<TheStep, ExpectedLhs, ExpectedRhs>()`. That forces the solver to
// report against terms *you* wrote, so the mismatch is legible. This is how the
// wrong middle term in `Successor::MulSucc` was found.

/// Forces the trait solver to produce, and check, the Gauss proof for `N`.
///
/// ```
/// use curryhoward::gaussian::*;
/// check_gauss::<Ten>();
/// ```
pub fn check_gauss<N: Gaussian>()
where
    <N as Gaussian>::Proof: ProofOf<Equal<Product<N, Successor<N>>, Double<Triangle<N>>>>,
{
}

/// Forces `L = R` to be witnessed by `P`.
///
/// This is where the Curry-Howard correspondence becomes concrete: the call
/// compiles exactly when `P` really is a proof of `L = R`. `rustc` is the
/// proof checker, and a type error is a rejected proof.
///
/// A true statement, correctly witnessed:
///
/// ```
/// use curryhoward::gaussian::*;
/// check::<Refl<Three>, Sum<One, Two>, Three>();
/// ```
///
/// A false statement is rejected — `1 + 2` is not `2`:
///
/// ```compile_fail
/// use curryhoward::gaussian::*;
/// check::<Refl<Two>, Sum<One, Two>, Two>();
/// ```
///
/// Being *true* is not enough; the witness must actually prove it. `N + 0 = N`
/// holds for every `N`, but `Refl` cannot show it, because `Sum<N, Zero>` does
/// not reduce to `N` without knowing whether `N` is `Zero` or a `Successor`:
///
/// ```compile_fail
/// use curryhoward::gaussian::*;
/// fn bad<N: Number>() {
///     check::<Refl<N>, Sum<N, Zero>, N>();
/// }
/// ```
///
/// The inductive witness does prove it:
///
/// ```
/// use curryhoward::gaussian::*;
/// fn good<N: Number>() {
///     check::<<N as Number>::AddZero, Sum<N, Zero>, N>();
/// }
/// ```
///
/// And the trusted base cannot be extended from outside: `ProofOf` is sealed,
/// so no downstream crate can assert a new axiom and prove `0 = 1`.
///
/// ```compile_fail
/// use curryhoward::gaussian::*;
/// struct Cheat;
/// impl ProofOf<Equal<Zero, One>> for Cheat {}
/// ```
pub fn check<P, L, R>()
where
    P: ProofOf<Equal<L, R>>,
{
}

// ============================================================================
// EXAMPLES — small proofs, in increasing order of effort
// ============================================================================

pub mod examples {
    use super::*;

    // -- Level 0: nothing to prove ------------------------------------------
    //
    // Rust normalizes associated types, so any equation between *concrete*
    // numbers already holds definitionally: both sides reduce to the same
    // type, and `Refl` closes it. No induction, no rewriting.

    /// `1 + 2 = 3`
    pub type OnePlusTwo = Refl<Three>;

    /// `2 * 4 = 8`
    pub type TwoTimesFour = Refl<Eight>;

    /// `T(4) = 10` — the triangular number 1+2+3+4.
    pub type TriangleFour = Refl<Ten>;

    // -- Level 1: one law, applied ------------------------------------------
    //
    // Once a variable `N` appears, normalization stalls: `Sum<N, Zero>` cannot
    // reduce without knowing whether `N` is `Zero` or a `Successor`. That is
    // exactly where the inductive witnesses on `Number` come in.

    /// `0 + N = N` — still definitional: `Zero::Add<Rhs> = Rhs` by definition.
    pub type ZeroPlusN<N: Number> = Refl<N>;

    /// `N + 0 = N` — *not* definitional, because the recursion is on the left
    /// argument. Needs the inductive witness.
    pub type NPlusZero<N: Number> = <N as Number>::AddZero;

    /// `N + 2 = 2 + N`
    pub type NPlusTwo<N: Number> = <N as Number>::AddComm<Two>;

    // -- Level 2: composing two steps ---------------------------------------

    /// `N + 1 = N + 1` in the other spelling: `Sum<N, One> = Successor<N>`.
    ///
    /// Two rewrites chained with `Trans`. Note the explicit middle term — the
    /// solver cannot infer it, so `Trans` takes it as a parameter:
    ///
    /// ```text
    ///   N + 1
    /// = (N + 0) + 1   by AddSucc
    /// = N + 1         by AddZero, under a Successor (SuccCong)
    /// ```
    pub type AddOneIsSucc<N: Number> = Trans<
        <N as Number>::AddSucc<Zero>,
        SuccCong<Sum<N, Zero>, N, <N as Number>::AddZero>,
        Successor<Sum<N, Zero>>,
    >;

    /// `2 * N = N + N`
    ///
    /// `Product<Two, N>` normalizes to `Sum<N, Sum<N, Zero>>`, so only the
    /// inner `N + 0` needs rewriting — one congruence, no `Trans`.
    pub type TwoTimesN<N: Number> = AddCongLeft<N, Sum<N, Zero>, N, <N as Number>::AddZero>;

    // -- Level 3: reusing a theorem -----------------------------------------

    /// Gauss in its more familiar shape: `N * (N + 1) = 2 * T(N)`.
    ///
    /// [`Gaussian::Proof`] gives `N(N+1) = T(N) + T(N)`; [`TwoTimesN`] turns
    /// `2 * T(N)` into `T(N) + T(N)`, and `Sym` runs it backwards.
    pub type GaussTwoTimes<N: Gaussian> =
        Trans<<N as Gaussian>::Proof, Sym<TwoTimesN<Triangle<N>>>, Double<Triangle<N>>>;
}

#[cfg(test)]
mod tests {
    use super::examples::*;
    use super::*;

    #[test]
    fn concrete_arithmetic_is_definitional() {
        check::<OnePlusTwo, Sum<One, Two>, Three>();
        check::<TwoTimesFour, Product<Two, Four>, Eight>();
        check::<TriangleFour, Triangle<Four>, Ten>();
    }

    #[test]
    fn laws_hold_for_every_n() {
        fn all<N: Number>() {
            check::<ZeroPlusN<N>, Sum<Zero, N>, N>();
            check::<NPlusZero<N>, Sum<N, Zero>, N>();
            check::<NPlusTwo<N>, Sum<N, Two>, Sum<Two, N>>();
            check::<AddOneIsSucc<N>, Sum<N, One>, Successor<N>>();
            check::<TwoTimesN<N>, Product<Two, N>, Double<N>>();
        }
        all::<Zero>();
        all::<Five>();
    }

    #[test]
    fn gauss_in_familiar_form() {
        fn all<N: Gaussian>() {
            check::<GaussTwoTimes<N>, Product<N, Successor<N>>, Product<Two, Triangle<N>>>();
        }
        all::<Zero>();
        all::<Four>();
    }

    #[test]
    fn arithmetic_computes() {
        check::<Refl<Three>, Sum<One, Two>, Three>();
        check::<Refl<Six>, Triangle<Three>, Six>();
        check::<Refl<Eight>, Product<Two, Four>, Eight>();
    }

    #[test]
    fn gauss_holds_for_concrete_naturals() {
        check_gauss::<Zero>();
        check_gauss::<Three>();
        check_gauss::<Ten>();
    }

    // The universally quantified statement: this compiles only because the
    // inductive `impl<N: Gaussian> Gaussian for Successor<N>` type-checks for
    // every `N`, so the theorem holds for all Peano naturals, not just the
    // ones instantiated above.
    fn gauss_holds_for_all<N: Gaussian>() {
        check_gauss::<N>();
    }
}
