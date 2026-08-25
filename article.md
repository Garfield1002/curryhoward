# Curry-Howard in Rust: Proving Gauss's Theorem with the Type System

08/2026 - [source](https://github.com/Garfield1002/curryhoward)

## Introduction

The **[Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)** tells us we can write proofs using code,
more specifically, using a strong type system.
But can we ?
I hear rust has a strong type system..

## Using Rust to prove things

If you are a Rust enjoyer, prepare to witness a carnage.

### Axioms

Let's start with a solid foundation of things we all agree are true and don't
want to / can't prove.
These are our **axioms**.

In rust, we'll seal them in a private module so we can't add any later.

```rs
pub trait Axiom: private::Sealed {}
```

#### Equality

Since we are working with numbers, the main thing we want to prove today is equality:

```rs
pub struct Equal<L, R>(PhantomData<(L, R)>);
```

However, anybody can build a struct `Equal` with any value.

What we want is for our axioms to "build" that type.
For that we'll add a new trait:

```rs
pub trait ProofOf<Proposition>: Axiom {}
```

So if we can build a `ProofOf<Equal<X, Y>>` then that means our axioms are
sufficient to prove that `X = Y`.

Users can't just create a `ProofOf` without using axioms since we sealed the type.

#### Actual axioms

So how can we build equalities ?

Our first proper axiom (or proof strategy), is that a thing is always equal to
itself.
That is called reflexivity, and in logic is written `⊢ T = T`.
In rust, we'll write it:

```rs
pub struct Refl<T>(PhantomData<T>);
impl<T> private::Sealed for Refl<T> {}
impl<T> Axiom for Refl<T> {}
impl<T> ProofOf<Equal<T, T>> for Refl<T> {}
```
The important line is that it builds us a proof that `T=T`: `ProofOf<Equal<T, T>>`.

Some other properties require a starting hypothesis.
For example, symmetry: _if L = R then R = L_ or for a logician: `L = R ⊢ R = L`.
This is how we'll write it in rust:

```rs
pub struct Sym<P>(PhantomData<P>);
...
impl<L, R, P> ProofOf<Equal<R, L>> for Sym<P> where P: ProofOf<Equal<L, R>> {}
```
(I left out the sealed/axiom markers).
This one's fun, if we provide `Sym` with a proof `P` that `L=R`, it will give us a proof that `R=L`.

We can also have multiple hypothesis like with transitivity.
Transitivity says, _if L = M and M = R then L = R_.
Again in rust:

```rs
pub struct Trans<P, Q, Middle>(PhantomData<(P, Q, Middle)>);
...
impl<L, Middle, R, P, Q> ProofOf<Equal<L, R>> for Trans<P, Q, Middle>
where
    P: ProofOf<Equal<L, Middle>>,
    Q: ProofOf<Equal<Middle, R>>,
{
}
```
Here we need to provide `Trans` with a proof `P` that `L=Middle` and a proof `Q`
that `Middle = R` and it mints us a proof that `L = R` (`ProofOf<Equal<L, R>>`).

The last axiom we need is congruence.
For any well defined function `F`, if `A = B` then `F(A) = F(B)`.
Or in rust:
```rs
pub struct Cong<F, A, B, P>(PhantomData<(F, A, B, P)>);
impl<F, A, B, P> ProofOf<Equal<F::Apply<A>, F::Apply<B>>> for Cong<F, A, B, P>
where
    F: TypeFn,
    A: Number,
    B: Number,
    P: ProofOf<Equal<A, B>>,
{
}
```

`TypeFn` is the `F`, and we'll build it in a minute.
Rust has no type-level lambdas, so this looks quite bad..

#### Recap

And that's the whole trust base.
Four rules:

| Rule    | Statement               |
|---------|-------------------------|
| `Refl`  | `⊢ T = T`               |
| `Sym`   | `L = R ⊢ R = L`         |
| `Trans` | `L = M, M = R ⊢ L = R`  |
| `Cong`  | `A = B ⊢ F(A) = F(B)`   |

Everything from here on is *derived*: we only compose these four, and rustc
checks that we composed them correctly.

Which is a good moment to admit what "axiom" is really doing here.
Nothing forces `ProofOf<Equal<L, R>>` to mean that `L` and `R` are the same
type.
That reading is a promise I made, and the four impls above are me swearing that
each rule keeps the promise.

Also, these are axioms because I'm lazy and writing this in rust, I'm sure you
could probably do better.
Think of this as I didn't want to prove it, not it's unprovable.

### Numbers

We have some cool toys to prove equality, but no numbers.
Let's add some using Peano's construction.
A number is either 0 or the successor of a number.
Again we can't really force that in rust, so we'll allow successors of anything.

```rs
pub struct Zero;
pub struct Successor<N>(PhantomData<N>);
```

We can then add some numbers to use in our examples:

```rs
pub type One = Successor<Zero>;
pub type Two = Successor<One>;
pub type Three = Successor<Two>;
// ... and so on up to Ten
```

That's it, ez.

### Operators

We have numbers, let's do operators now.
We want addition, multiplication, and the triangular function for later.
Triangular function is just `T(n) = n + (n - 1) + ... + 1 + 0`

```rs
pub trait Arithmetic: Sized {
    type Add<Rhs: Number>: Number;
    type Mul<Rhs: Number>: Number;
    type Triangle: Number;
}

pub type Sum<L, R> = <L as Arithmetic>::Add<R>;
pub type Product<L, R> = <L as Arithmetic>::Mul<R>;
pub type Triangle<N> = <N as Arithmetic>::Triangle;
pub type Double<N> = Sum<N, N>;
```
Ok and now to say how they work, we just use the usual Peano recursion, one impl per constructor:

```rs
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
```

For 0 everything is easy, for a successor, we need to do some work.
```
(N + 1) + Rhs = (N + Rhs) + 1
(N + 1) * Rhs = (N * Rhs) + Rhs
T(N + 1) = (N + 1) + T(N)
```

### Free proofs

Before writing any real proof, let's see what we get for nothing.

We need one more helper (the one that actually makes this Curry-Howard):

```rs
pub fn check<P, L, R>()
where
    P: ProofOf<Equal<L, R>>,
{
}
```

An empty function with a where clause. That's the entire proof checker.
`check::<P, L, R>()` compiles exactly when `P` really is a proof that `L = R`.
Propositions are types, proofs are types, and proof checking is trait solving.
A type error is a rejected proof.

Now, the nice surprise: rustc normalizes associated types.
`Sum<One, Two>` and `Three` don't just have the same value, they *are* the same
type.
So reflexivity alone settles every equation between concrete numbers:

```rs
check::<Refl<Three>, Sum<One, Two>, Three>();   // 1 + 2 = 3
check::<Refl<Eight>, Product<Two, Four>, Eight>(); // 2 * 4 = 8
check::<Refl<Ten>, Triangle<Four>, Ten>();      // T(4) = 10
```

That's it we've solved maths!
Three Theorems, zero effort, 100% confidence since rustc said it was true.

Also it does say no when we lie:

```rs
check::<Refl<Two>, Sum<One, Two>, Two>();       // does not compile
```

We have a computer proving things!

### Where it stops being free

Replace a concrete number with a variable and normalization stalls:

```rs
fn bad<N: Number>() {
    check::<Refl<N>, Sum<N, Zero>, N>();        // does not compile
}
```

`n + 0 = n` is true for every `N`, but `Sum<N, Zero>` cannot reduce, because
reducing it means knowing whether `N` is `Zero` or a `Successor`, and it's
neither: it's a variable.

Meanwhile `0 + n = n` *is* free, because `Zero::Add<Rhs> = Rhs` fires without
looking at `Rhs`.
That asymmetry is entirely due to `Add` recursing on the left.
One of these two identical-looking statements is definitional, the other needs a
proof by induction.

So: time for proofs by inductions!

### Numbers that carry their own proofs

You already know how.
A recursive impl **is** an induction principle.

The trick is to make the laws part of what it means to be a number.
Each associated type below is a proof obligation, and the bound on it is checked at every impl:

```rs
pub trait Number: Arithmetic + Sized {
    type AddZero: ProofOf<Equal<Sum<Self, Zero>, Self>>;

    type AddSucc<R: Number>: ProofOf<Equal<Sum<Self, Successor<R>>, Successor<Sum<Self, R>>>>;

    type AddAssoc<B: Number, C: Number>: ProofOf<Equal<Sum<Sum<Self, B>, C>, Sum<Self, Sum<B, C>>>>;

    type AddComm<R: Number>: ProofOf<Equal<Sum<Self, R>, Sum<R, Self>>>;

    type MulSucc<R: Number>: ProofOf<Equal<Product<Self, Successor<R>>, Sum<Self, Product<Self, R>>>>;
}
```

Nothing can be a `Number` unless it proves all five laws.
(We haven't provent this yet we're just saying Numbers should follow this law)

Before we can fill them in we need the `TypeFn` I promised, so `Cong` has
something to rewrite under:

```rs
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
// ... AddRightFn, MulLeftFn, same shape

/// `A = B ⊢ A + 1 = B + 1`
pub type SuccCong<A, B, P> = Cong<SuccFn, A, B, P>;
/// `A = B ⊢ L + A = L + B`
pub type AddCongLeft<L, A, B, P> = Cong<AddLeftFn<L>, A, B, P>;
/// `A = B ⊢ A + R = B + R`
pub type AddCongRight<A, B, R, P> = Cong<AddRightFn<R>, A, B, P>;
```

All of this is just an ugly hack, just names.
But I don't want you to feel like I'm hiding something under the rug.

Back to our induction.
Let's start with the base case.
Here, Everything is definitional and `Refl` does most of the work.
The only case where we have to do something is for AddComm
Here we start from AddZero: `⊢ T + 0 = T` use symmetry to get `⊢ T = T + 0`
and this is definitionnaly equal to `⊢ 0 + T = T + 0`.
(Nottice how we had to be very verbose, it HAD to be `0 + T = T + 0`, `T + 0 = 0 + T` would not have worked).

```rs
impl Number for Zero {
    type AddZero = Refl<Zero>;
    type AddSucc<R: Number> = Refl<Successor<R>>;
    type AddAssoc<B: Number, C: Number> = Refl<Sum<B, C>>;
    type AddComm<R: Number> = Sym<<R as Number>::AddZero>;
    type MulSucc<R: Number> = Refl<Zero>;
}
```

Now for the inductive step, where the fun proofs actually live:

```rs
impl<N: Number> Number for Successor<N> {
    type AddZero = SuccCong<Sum<N, Zero>, N, <N as Number>::AddZero>;

    type AddComm<R: Number> = Trans<
        SuccCong<Sum<N, R>, Sum<R, N>, <N as Number>::AddComm<R>>,
        Sym<<R as Number>::AddSucc<N>>,
        Successor<Sum<R, N>>,
    >;
    // ... and three more
}
```

In `AddZero`, the recursive `<N as Number>::AddZero` **is** the induction
hypothesis, handed to us by the trait solver.
Reading the proof out we have `N + 0 = N ⊢ (N + 0) + 1 = N + 1`

rustc checks this impl **once**, generically in `N`.
Because it holds for an arbitrary `N`, the law holds for every Peano natural!
That's a genuine ∀-statement, checked at compile time, and it's honestly a bit magical that the trait solver does it at all.

Ok, let's do another one.
Our **goal** is to prove that `(N + 1) + R = R + (N + 1)`
We will use a transitive arbument.
- First, we show using congruence and our induction hypothesis that `N + R = R + N ⊢ (N + R) + 1 = (R + N) + 1`.
And by definition we get `(N + 1) + R = (R + N) + 1`
- Then we show using AddSucc that `⊢ R + (N + 1) = (R + N) + 1` and then we flip it with symetry `⊢ (R + N) + 1 = R + (N + 1)`.
We have two things equal to `(R + N) + 1`, so by transitivity we get: `(N + 1) + R = R + (N + 1)`

### Lemmas

With the five laws in hand we can start deriving. Rearranging sums is the boring
part of any arithmetic proof, so let's get it over with:

```rs
/// `A + (B + C) = B + (A + C)`
pub type SwapFront<A, B, C> = Trans<
    Sym<<A as Number>::AddAssoc<B, C>>,
    Trans<
        AddCongRight<Sum<A, B>, Sum<B, A>, C, <A as Number>::AddComm<B>>,
        <B as Number>::AddAssoc<A, C>,
        Sum<Sum<B, A>, C>,
    >,
    Sum<Sum<A, B>, C>,
>;

/// `(A + B) + (C + D) = (A + C) + (B + D)`
pub type Shuffle<A, B, C, D> = Trans<
    <A as Number>::AddAssoc<B, Sum<C, D>>,
    Trans<
        AddCongLeft<A, Sum<B, Sum<C, D>>, Sum<C, Sum<B, D>>, SwapFront<B, C, D>>,
        Sym<<A as Number>::AddAssoc<C, Sum<B, D>>>,
        Sum<A, Sum<B, Sum<C, D>>>,
    >,
    Sum<A, Sum<B, Sum<C, D>>>,
>;
```

Plus one small one we'll need, `(N + 2) + N = (N + 1) + (N + 1)`:

```rs
pub type SuccPair<N> =
    SuccCong<Successor<Sum<N, N>>, Sum<N, Successor<N>>, Sym<<N as Number>::AddSucc<N>>>;
```

`SwapFront` says *move a term one slot to the left*. Nine lines of nested `Trans`
and `Cong`, of which the only informative parts are `AddAssoc` and `AddComm`.
The rest is bookkeeping: two middle terms written out by hand because the solver
won't guess them.


There it is. The carnage.
I'll spare you the details, lets just say they're left as an exercise to the motivated reader.


### The Big Theorem we want to prove

Gauss's theorem (the sum of the first n positive integers but we need to make this sound cool), in the shape that's convenient here: `n(n + 1) = T(n) + T(n)`.

```rs
pub trait Gaussian: Number {
    type Proof: ProofOf<Equal<Product<Self, Successor<Self>>, Double<Triangle<Self>>>>;
}

impl Gaussian for Zero {
    type Proof = Refl<Zero>;
}
```

`0 * 1 = 0 = T(0) + T(0)`, all concrete, so `Refl` again.

For the inductive step, here is the proof as a VERY attention focused human would write it:

```
  (N+1)(N+2)
= (N+2) + N(N+2)              by definition of *
= (N+2) + (N + N(N+1))        by MulSucc
= (N+2) + (N + 2T(N))         by the induction hypothesis
= ((N+2) + N) + 2T(N)         by associativity
= ((N+1) + (N+1)) + 2T(N)     by SuccPair
= ((N+1) + T(N)) + ((N+1) + T(N))
                              by Shuffle
= T(N+1) + T(N+1)             by definition of Triangle
```

Five rewrites. Nothing clever, and no step you'd need to think hard about.

Here is the same thing in Rust. First the five steps, each one a `Cong` telling
the solver where to rewrite:

```rs
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
```

Then, because `Trans` demands its middle term, we have to name every intermediate
expression in the chain:

```rs
type GaussM1<N: Number> = Sum<Successor<Successor<N>>, Sum<N, Product<N, Successor<N>>>>;
type GaussM2<N: Number> = Sum<Successor<Successor<N>>, Sum<N, Double<Triangle<N>>>>;
type GaussM3<N: Number> = Sum<Sum<Successor<Successor<N>>, N>, Double<Triangle<N>>>;
type GaussM4<N: Number> = Sum<Sum<Successor<N>, Successor<N>>, Double<Triangle<N>>>;
```

Those four lines are the middle column of the human proof above, transcribed by
hand.
They carry no logical content whatsoever.
They exist purely so the solver knows which type to look at next.

And then we staple it together:

```rs
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
```

That's it. That last impl is a theorem about all natural numbers, and it is
checked by `cargo test` (`check_gauss` being `check` with the theorem's
statement baked in):

```rs
check_gauss::<Ten>();

fn gauss_holds_for_all<N: Gaussian>() {
    check_gauss::<N>();
}
```

The second one is the real prize. It compiles, generically in `N`, so Gauss's
theorem holds for every Peano natural. rustc proved it.

### What it cost

It works.
It took me a minute.
Nobody should do this.
In no particular order:

- **`Trans` needs its middle term.**. Every chain of trans comes with a list of
required intermediate steps.
- **We can't make functions of types of types**. The whole `Cong` and `TypeFn` are akward.
We'd need traits which can take trait params.
- **Errors are terrible.** Here I replaced a random N by a 1 in the proof
```
type mismatch resolving `<AddLeftFn<...> as TypeFn>::Apply<...> == Successor<...>`
expected struct `Successor<Successor<<N as Arithmetic>::Add<...>>>`
   found struct `Successor<Successor<<N as Arithmetic>::Add<Successor<...>>>>`
consider constraining the associated type `<N as gaussian::Arithmetic>::Add<<<N as gaussian::Arithmetic>::Triangle as gaussian::Arithmetic>::Add<<N as gaussian::Arithmetic>::Triangle>>` to `gaussian::Successor<<<N as gaussian::Arithmetic>::Triangle as gaussian::Arithmetic>::Add<<N as gaussian::Arithmetic>::Triangle>>`
for more information, visit https://doc.rust-lang.org/book/ch19-03-advanced-traits.html
associated types for the current `impl` cannot be restricted in `where` clauses
1 redundant requirement hidden
required for `Trans<Cong<AddLeftFn<Successor<...>>, ..., ..., ...>, ..., ...>` to implement `ProofOf<Equal<Successor<Successor<<N as Arithmetic>::Add<...>>>, ...>>`
the full name for the type has been written to '/home/jack/dev/curryhoward/target/debug/deps/curryhoward-72d06ad021dde884.long-type-3211403651737931667.txt'
consider using `--verbose` to print the full type name to the console
gaussian.rs(198, 29): expected this to be `gaussian::Successor<gaussian::Successor<<N as gaussian::Arithmetic>::Add<<N as gaussian::Arithmetic>::Add<<<N as gaussian::Arithmetic>::Triangle as gaussian::Arithmetic>::Add<<N as gaussian::Arithmetic>::Triangle>>>>>`
gaussian.rs(89, 30): required for `Trans<Cong<AddLeftFn<Successor<...>>, ..., ..., ...>, ..., ...>` to implement `ProofOf<Equal<Successor<Successor<<N as Arithmetic>::Add<...>>>, ...>>`
gaussian.rs(298, 17): required by a bound in `gaussian::Gaussian::Proof`
```
- **And finally the axioms are just vibes.**

~500 lines of Rust, four axioms.

## LEAN

Now let's do it in a language designed for this.

Same Peano numbers, same left-recursive definitions, so the comparison is fair:

```lean
inductive Num where
  | zero : Num
  | succ : Num → Num

def add : Num → Num → Num
  | zero,   r => r
  | succ l, r => succ (add l r)

def mul : Num → Num → Num
  | zero,   _ => zero
  | succ l, r => add r (mul l r)

def triangle : Num → Num
  | zero   => zero
  | succ n => add (succ n) (triangle n)
```

These even look like functions!

Now, the axioms. Remember our four rules, the ones we had to swear to ?
Here is the entire equality machinery in Lean:

```lean
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
```

One inductive definition, one constructor. Our `Refl` is that constructor. The
other three we swore to are *theorems*:

| Ours (asserted) | Lean's (derived)           |
|-----------------|----------------------------|
| `Refl`          | `Eq.refl`                  |
| `Sym`           | `Eq.symm`                  |
| `Trans`         | `Eq.trans`                 |
| `Cong`          | `congrArg`                 |

So: same five laws.
Same proofs (
    I asked AI for a line by line translation of the Rust, you could probably do better).

```lean
theorem add_zero : ∀ n : Num, n + zero = n
  | zero   => rfl
  | succ n => congrArg succ (add_zero n)

theorem add_succ : ∀ l r : Num, l + succ r = succ (l + r)
  | zero,   _ => rfl
  | succ l, r => congrArg succ (add_succ l r)

theorem add_assoc : ∀ a b c : Num, (a + b) + c = a + (b + c)
  | zero,   _, _ => rfl
  | succ a, b, c => congrArg succ (add_assoc a b c)

theorem add_comm : ∀ a b : Num, a + b = b + a
  | zero,   b => (add_zero b).symm
  | succ a, b => (congrArg succ (add_comm a b)).trans (add_succ b a).symm
```

Compare `add_comm` with the Rust version from earlier.
It's the same proof: congruence on the induction hypothesis, then symmetry of `AddSucc`. Except the middle term is inferred.
Also `succ` is a function so no `SuccFn` struct is needed, and the recursive call is the induction hypothesis.

```lean
theorem swap_front (a b c : Num) : a + (b + c) = b + (a + c) :=
  ((add_assoc a b c).symm.trans
    (congrArg (· + c) (add_comm a b))).trans (add_assoc b a c)

theorem mul_succ : ∀ l r : Num, l * succ r = l + l * r
  | zero,   _ => rfl
  | succ l, r =>
    (congrArg (succ r + ·) (mul_succ l r)).trans
      (congrArg succ (swap_front r l (l * r)))
```

`(· + c)` and `(succ r + ·)` are the type-level lambdas we couldn't have.
`Shuffle` and `SuccPair` go the same way, three lines and one line.

And the theorem. `calc` lets us write the chain as the middle column of the human
proof, which is exactly what `GaussM1`..`GaussM4` were failing to be:

```lean
theorem gauss : ∀ n : Num, n * succ n = triangle n + triangle n
  | zero   => rfl
  | succ n =>
    calc succ n * succ (succ n)
      _ = succ (succ n) + (n + n * succ n) :=
            congrArg (succ (succ n) + ·) (mul_succ n (succ n))
      _ = succ (succ n) + (n + (triangle n + triangle n)) :=
            congrArg (fun x => succ (succ n) + (n + x)) (gauss n)
      _ = (succ (succ n) + n) + (triangle n + triangle n) :=
            (add_assoc _ n _).symm
      _ = (succ n + succ n) + (triangle n + triangle n) :=
            congrArg (· + (triangle n + triangle n)) (succ_pair n)
      _ = triangle (succ n) + triangle (succ n) :=
            shuffle (succ n) (succ n) (triangle n) (triangle n)
```

Kinkda sorta more readable.

The steps on the left are the equations. The proofs on the right are the five
rewrites.
Nothing else.
And we can ask Lean what we took on trust:

```
$ lean gauss.lean
'Num.gauss' does not depend on any axioms
```

49 lines against ~500, zero axioms against four..

For completeness, on the standard library's `Nat`, with tactics allowed, the
whole thing is:

```lean
def T : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + T n

theorem gauss_nat (n : Nat) : n * (n + 1) = T n + T n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [T, Nat.mul_succ, Nat.succ_mul] at *; omega
```

Four lines, and `omega` does the arithmetic.
This is the part where the comparison stops being a fun comparison.

## So, can a computer prove things ?

Yes, and Rust's type system really is strong enough!
The `gauss_holds_for_all` above is a theorem about infinitely many numbers, checked by `cargo test` (in a finite amount of time, so I guess it's blazingly fast 🚀).
Curry-Howard isn't a metaphor here.
Propositions really are types, proofs really are types, (everything is a type), and the trait solver really is a proof checker.

But it's a proof checker with no proof *assistant* attached, and that's the whole
difference.
Everything in rust was painful.
- the middle terms
- the lack of functions
- the `GaussM` steps
-  the unreadable errors
None of that in a real proof assistant.

Rust's trait solver deliberately doesn't do proof search, because it's meant to
resolve method calls, and suprisingly, not do prove theorems ?

All of this is a very very long way of saying: the Curry-Howard correspondence is real.
Rust proves it, and you should use Lean.
And I need a vacation!

The code is at [`src/gaussian.rs`](src/gaussian.rs) and
[`gauss.lean`](gauss.lean).
`cargo test` runs 11 tests, three of which must fail to compile.
