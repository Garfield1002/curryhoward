/-!
# Gauss's theorem in Lean, as a line-for-line mirror of `src/gaussian.rs`

Same Peano naturals, same left-recursive definitions, same five laws, same five
rewrites in the inductive step. Everything is in **term mode** — no tactics — so
this is a translation of the Rust proof and not a demonstration of Lean's
automation.

The four rules the Rust version has to *assert* (`Refl`, `Sym`, `Trans`, `Cong`)
appear here as `rfl`, `Eq.symm`, `Eq.trans` and `congrArg`, all of them theorems
derived from a single inductive definition of `Eq`. `#print axioms gauss` at the
bottom confirms the trusted base is empty.

Check it with:

    elan run leanprover/lean4:v4.31.0 lean gauss.lean
-/

/-- The same Peano naturals as the Rust version. -/
inductive Num where
  | zero : Num
  | succ : Num → Num

namespace Num

/-- Recursion on the *left* argument, exactly as in the Rust `Arithmetic` impl.
That is what makes `zero + r = r` definitional and `n + zero = n` a theorem. -/
def add : Num → Num → Num
  | zero,   r => r
  | succ l, r => succ (add l r)

def mul : Num → Num → Num
  | zero,   _ => zero
  | succ l, r => add r (mul l r)

def triangle : Num → Num
  | zero   => zero
  | succ n => add (succ n) (triangle n)

instance : Add Num := ⟨add⟩
instance : Mul Num := ⟨mul⟩

-- ---------------------------------------------------------------------------
-- The five laws the Rust `Number` trait carries as proof obligations.
-- ---------------------------------------------------------------------------

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

/-- `a + (b + c) = b + (a + c)` — the Rust `SwapFront`. -/
theorem swap_front (a b c : Num) : a + (b + c) = b + (a + c) :=
  ((add_assoc a b c).symm.trans
    (congrArg (· + c) (add_comm a b))).trans (add_assoc b a c)

theorem mul_succ : ∀ l r : Num, l * succ r = l + l * r
  | zero,   _ => rfl
  | succ l, r =>
    (congrArg (succ r + ·) (mul_succ l r)).trans
      (congrArg succ (swap_front r l (l * r)))

-- ---------------------------------------------------------------------------
-- Rearrangement lemmas.
-- ---------------------------------------------------------------------------

/-- `(a + b) + (c + d) = (a + c) + (b + d)` — the Rust `Shuffle`. -/
theorem shuffle (a b c d : Num) : (a + b) + (c + d) = (a + c) + (b + d) :=
  ((add_assoc a b (c + d)).trans
    (congrArg (a + ·) (swap_front b c d))).trans (add_assoc a c (b + d)).symm

/-- `(n + 2) + n = (n + 1) + (n + 1)` — the Rust `SuccPair`. -/
theorem succ_pair (n : Num) : succ (succ n) + n = succ n + succ n :=
  (add_succ (succ n) n).symm

-- ---------------------------------------------------------------------------
-- The theorem. The `calc` chain is the Rust `GaussM1`..`GaussM4`, except here
-- the intermediate terms are the proof rather than scaffolding for it.
-- ---------------------------------------------------------------------------

/-- Gauss: `n * (n + 1) = T(n) + T(n)`, for every `Num`. -/
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

-- Expected: `'gauss' does not depend on any axioms`.
#print axioms gauss

end Num

-- ---------------------------------------------------------------------------
-- For contrast: the standard library's `Nat`, with tactics allowed.
-- ---------------------------------------------------------------------------

def T : Nat → Nat
  | 0     => 0
  | n + 1 => (n + 1) + T n

theorem gauss_nat (n : Nat) : n * (n + 1) = T n + T n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [T, Nat.mul_succ, Nat.succ_mul] at *; omega
