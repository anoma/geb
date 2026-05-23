import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.Utilities.Tower

/-!
# K^sim-Derived Arithmetic

`KMor1`-level versions of basic arithmetic functions: `pred`,
`isZero`, `add`, `double`, `cond`, `notEq1`, `mult`, `monus`,
`pow2`, `mod`, `div`, `divNat`.  Each function carries an
`@[simp]`-marked correctness theorem linking its interpretation to
its `Nat` counterpart, plus a `level ≤ N` placement proof.

Every function is a closed-form `KMor1` term built from the
generators `zero`, `succ`, `proj`, `comp`, `simrec` (and the
non-simultaneous wrapper `rec1`); the `KMor1` inductive is not
extended.

Levels follow Tourlakis's classification (Notes Prop 10.2.12;
PR §0.1.0.17); `mod`, `div`, `divNat` are placed using
constructions in this module.

Sibling of `Utilities/ERArith.lean`; spec at
`docs/superpowers/specs/2026-05-05-karith-design.md`.
-/

namespace GebLean

/-- The constant `1` morphism at arity 0.

PR §0.1.0.17 implicit (constants and `succ` generate K^sim_0). -/
def KMor1.one : KMor1 0 :=
  KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.zero)

/-- Interpretation of `one`: always returns `1`. -/
@[simp] theorem KMor1.interp_one (ctx : Fin 0 → ℕ) :
    KMor1.one.interp ctx = 1 := rfl

example : KMor1.one.level = 0 := by decide

/-- Predecessor function as a `KMor1 1` term:
`pred(0) = 0`, `pred(x+1) = x`.

Tourlakis PR §0.1.0.17(4) (`λx.x ∸ 1 ∈ K_1`); Notes 10.2.12 row 2. -/
def KMor1.pred : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.proj ⟨0, by decide⟩)

private lemma KMor1.pred_aux (n : ℕ) :
    KMor1.pred.interp (Fin.cons n Fin.elim0) = n.pred := by
  induction n with
  | zero =>
    unfold KMor1.pred
    rw [KMor1.interp_rec1_zero]
    rfl
  | succ n _ =>
    unfold KMor1.pred
    rw [KMor1.interp_rec1_succ]
    rw [KMor1.interp_proj]
    rfl

/-- Interpretation of `pred`: `Nat.pred`. -/
@[simp] theorem KMor1.interp_pred (ctx : Fin 1 → ℕ) :
    KMor1.pred.interp ctx = (ctx 0).pred := by
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  rw [hctx]
  exact KMor1.pred_aux (ctx 0)

example : KMor1.pred.level = 1 := by decide

/-- Zero indicator: `isZero(0) = 1`, `isZero(x+1) = 0`.
Equivalently `1 ∸ x`.

Tourlakis PR §0.1.0.17(3) (`λx.1 ∸ x ∈ K_1`). -/
def KMor1.isZero : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.one)
    (g := KMor1.zero)

private lemma KMor1.isZero_aux (n : ℕ) :
    KMor1.isZero.interp (Fin.cons n Fin.elim0)
      = if n = 0 then 1 else 0 := by
  induction n with
  | zero =>
    unfold KMor1.isZero
    rw [KMor1.interp_rec1_zero]
    simp [KMor1.interp_one]
  | succ n _ =>
    unfold KMor1.isZero
    rw [KMor1.interp_rec1_succ]
    simp [KMor1.interp_zero]

/-- Interpretation of `isZero`: 1 if input is 0, else 0. -/
@[simp] theorem KMor1.interp_isZero (ctx : Fin 1 → ℕ) :
    KMor1.isZero.interp ctx = if ctx 0 = 0 then 1 else 0 := by
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  rw [hctx]
  exact KMor1.isZero_aux (ctx 0)

example : KMor1.isZero.level = 1 := by decide

/-- Addition: `add(0, y) = y`, `add(x+1, y) = succ(add(x, y))`.

Tourlakis PR §0.1.0.17(1); Notes 10.2.12 row 1. -/
def KMor1.add : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    (g := KMor1.comp KMor1.succ
            (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))

private lemma KMor1.add_aux (n : ℕ) (p : Fin 1 → ℕ) :
    KMor1.add.interp (Fin.cons n p) = n + p ⟨0, by decide⟩ := by
  induction n with
  | zero =>
    unfold KMor1.add
    rw [KMor1.interp_rec1_zero, KMor1.interp_proj]
    simp
  | succ n ih =>
    unfold KMor1.add
    rw [KMor1.interp_rec1_succ, KMor1.interp_comp,
        KMor1.interp_succ, KMor1.interp_proj]
    have hidx :
        (⟨2, KMor1.add._proof_2⟩ : Fin (1 + 1 + 1))
          = Fin.natAdd (1 + 1) (⟨0, by decide⟩ : Fin 1) := by
      apply Fin.ext; rfl
    rw [hidx, Fin.append_right]
    change ((KMor1.proj ⟨0, KMor1.add._proof_1⟩).rec1
              (KMor1.succ.comp
                (fun _ : Fin 1 =>
                  KMor1.proj ⟨2, KMor1.add._proof_2⟩))).interp
              (Fin.cons n p) + 1
          = n + 1 + p ⟨0, by decide⟩
    rw [show (KMor1.proj ⟨0, KMor1.add._proof_1⟩).rec1
              (KMor1.succ.comp
                (fun _ : Fin 1 =>
                  KMor1.proj ⟨2, KMor1.add._proof_2⟩))
            = KMor1.add from rfl]
    rw [ih]
    omega

/-- Interpretation of `add`: `ctx 0 + ctx 1`. -/
@[simp] theorem KMor1.interp_add (ctx : Fin 2 → ℕ) :
    KMor1.add.interp ctx = ctx 0 + ctx 1 := by
  have hctx :
      ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [hctx, KMor1.add_aux]
  rfl

example : KMor1.add.level = 1 := by decide

/-- Doubling: `double(0) = 0`, `double(x+1) = succ(succ(double(x)))`.

Derived at K^sim_1; used as the level-1 step in `pow2`. -/
def KMor1.double : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.comp KMor1.succ
            (fun _ : Fin 1 =>
              KMor1.comp KMor1.succ
                (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)))

private lemma KMor1.double_aux (n : ℕ) :
    KMor1.double.interp (Fin.cons n Fin.elim0) = 2 * n := by
  induction n with
  | zero =>
    unfold KMor1.double
    rw [KMor1.interp_rec1_zero]
    rfl
  | succ n ih =>
    unfold KMor1.double
    rw [KMor1.interp_rec1_succ, KMor1.interp_comp,
        KMor1.interp_succ, KMor1.interp_comp,
        KMor1.interp_succ, KMor1.interp_proj]
    have hidx :
        (⟨1, KMor1.double._proof_1⟩ : Fin (0 + 1 + 1))
          = Fin.natAdd (0 + 1) (⟨0, by decide⟩ : Fin 1) := by
      apply Fin.ext; rfl
    rw [hidx, Fin.append_right]
    change ((KMor1.zero (n := 0)).rec1
              (KMor1.succ.comp
                (fun _ : Fin 1 =>
                  KMor1.succ.comp
                    (fun _ : Fin 1 =>
                      KMor1.proj ⟨1, KMor1.double._proof_1⟩)))).interp
              (Fin.cons n Fin.elim0) + 1 + 1
          = 2 * (n + 1)
    rw [show (KMor1.zero (n := 0)).rec1
              (KMor1.succ.comp
                (fun _ : Fin 1 =>
                  KMor1.succ.comp
                    (fun _ : Fin 1 =>
                      KMor1.proj ⟨1, KMor1.double._proof_1⟩)))
            = KMor1.double from rfl]
    rw [ih]
    omega

/-- Interpretation of `double`: `2 * ctx 0`. -/
@[simp] theorem KMor1.interp_double (ctx : Fin 1 → ℕ) :
    KMor1.double.interp ctx = 2 * ctx 0 := by
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  rw [hctx]
  exact KMor1.double_aux (ctx 0)

example : KMor1.double.level = 1 := by decide

/-- Conditional / switch: `cond(0, y, z) = y`, `cond(x+1, y, z) = z`.

Tourlakis PR §0.1.0.17(6) (`switch`). -/
def KMor1.cond : KMor1 3 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    (g := KMor1.proj ⟨2, by decide⟩)

private lemma KMor1.cond_aux (n : ℕ) (p : Fin 2 → ℕ) :
    KMor1.cond.interp (Fin.cons n p)
      = if n = 0 then p ⟨0, by decide⟩ else p ⟨1, by decide⟩ := by
  cases n with
  | zero =>
    unfold KMor1.cond
    rw [KMor1.interp_rec1_zero, KMor1.interp_proj]
    rfl
  | succ n =>
    unfold KMor1.cond
    rw [KMor1.interp_rec1_succ, KMor1.interp_proj]
    have hidx : (⟨2, by decide⟩ : Fin (2 + 1 + 1))
        = Fin.castAdd 1 (⟨2, by decide⟩ : Fin (2 + 1)) := by
      apply Fin.ext; rfl
    rw [hidx, Fin.append_left]
    have hsucc : (⟨2, by decide⟩ : Fin (2 + 1))
        = Fin.succ (⟨1, by decide⟩ : Fin 2) := by
      apply Fin.ext; rfl
    rw [hsucc, Fin.cons_succ]
    rfl

/-- Interpretation of `cond`: `if ctx 0 = 0 then ctx 1 else ctx 2`. -/
@[simp] theorem KMor1.interp_cond (ctx : Fin 3 → ℕ) :
    KMor1.cond.interp ctx
      = if ctx 0 = 0 then ctx 1 else ctx 2 := by
  have hctx :
      ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  rw [hctx, KMor1.cond_aux]
  cases h : ctx 0 with
  | zero => rfl
  | succ n => rfl

example : KMor1.cond.level = 1 := by decide

/-- Constant-`c` morphism at arity 0, built by `c`-fold
composition of `KMor1.succ` over `KMor1.zero`. Level 0.

Tourlakis 2018 § 0.1.0.2 (p. 1): closure of `K_0 = {λx.x,
λx.x+1}` under substitution yields all natural-number
constants. GebLean's `KMor1.zero` is a separate constructor; the
`succ ∘ zero` pattern realises the same level-0 closure
principle. -/
def KMor1.natK : ℕ → KMor1 0
  | 0     => KMor1.zero
  | c + 1 =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.natK c)

/-- The interpretation of `KMor1.natK c` at the empty
context is `c`. -/
@[simp] theorem KMor1.interp_natK (c : ℕ) (ctx : Fin 0 → ℕ) :
    (KMor1.natK c).interp ctx = c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [KMor1.natK, KMor1.interp_comp, KMor1.interp_succ]
    rw [ih]

/-- `KMor1.natK c` has level 0 for every `c`. -/
theorem KMor1.natK_level (c : ℕ) : (KMor1.natK c).level = 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change KMor1.level
        (KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.natK c)) = 0
    unfold KMor1.level
    have hsup :
        Fin.maxOfNat 1 (fun _ : Fin 1 => (KMor1.natK c).level) ≤ 0 :=
      Fin.maxOfNat_le (by intro _; rw [ih])
    have hsucc : KMor1.level (KMor1.succ : KMor1 1) = 0 := rfl
    -- Goal contains `fun i : Fin 1 ↦ ((fun _ ↦ natK c) i).level`,
    -- which is beta-equal but not defeq to the bound in `hsup`;
    -- `simp only []` beta-normalises both sides for `omega`.
    simp only []
    omega

/-- The constant-`c` morphism at arity `n`, obtained by
composing `KMor1.natK c` with the empty family `Fin.elim0`.
Level 0. -/
def KMor1.natK' (n c : ℕ) : KMor1 n :=
  KMor1.comp (KMor1.natK c) Fin.elim0

/-- The interpretation of `KMor1.natK' n c` at any context is
`c`. -/
@[simp] theorem KMor1.interp_natK' (n c : ℕ) (ctx : Fin n → ℕ) :
    (KMor1.natK' n c).interp ctx = c := by
  simp only [KMor1.natK', KMor1.interp_comp, KMor1.interp_natK]

/-- `KMor1.natK' n c` has level 0 for every `n` and `c`. -/
theorem KMor1.natK'_level (n c : ℕ) :
    (KMor1.natK' n c).level = 0 := by
  change KMor1.level (KMor1.comp (KMor1.natK c) Fin.elim0) = 0
  unfold KMor1.level
  rw [KMor1.natK_level]
  rfl

/-- Characteristic of the predicate `x ≠ 1` (Tourlakis
predicate-as-zero convention): `notEq1(x) = 0` when `x ≠ 1`,
`notEq1(x) = 1` when `x = 1`.

Construction: `isZero(pred(x) + isZero(x))`. The inner sum vanishes
exactly at `x = 1` (since `pred(1) = 0` and `isZero(1) = 0`).

The name refers to the predicate being characterized. Per
Tourlakis convention, the value is 0 when the predicate holds.

Tourlakis PR §0.1.0.20 (`λx.x = a ∈ K_{1,*}`) plus Notes 10.2.14
(Boolean closure of K_{n,*}). -/
def KMor1.notEq1 : KMor1 1 :=
  KMor1.comp KMor1.isZero (fun _ : Fin 1 =>
    KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.pred
      | ⟨1, _⟩ => KMor1.isZero))

/-- Interpretation of `notEq1`: `1` if `ctx 0 = 1`, else `0`. -/
@[simp] theorem KMor1.interp_notEq1 (ctx : Fin 1 → ℕ) :
    KMor1.notEq1.interp ctx = if ctx 0 = 1 then 1 else 0 := by
  unfold KMor1.notEq1
  rw [KMor1.interp_comp, KMor1.interp_isZero,
      KMor1.interp_comp, KMor1.interp_add,
      KMor1.interp_pred, KMor1.interp_isZero]
  rcases h : ctx 0 with _ | _ | n
  · simp
  · simp
  · simp

example : KMor1.notEq1.level = 1 := by decide

/-- Multiplication: `mult(0, y) = 0`, `mult(x+1, y) = y + mult(x, y)`.

Tourlakis PR §0.1.0.17(b); Notes 10.2.12 row 4. -/
def KMor1.mult : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.zero)
    (g := KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
      | ⟨1, _⟩ => KMor1.proj ⟨2, by decide⟩))

private lemma KMor1.mult_aux (n : ℕ) (p : Fin 1 → ℕ) :
    KMor1.mult.interp (Fin.cons n p) = n * p ⟨0, by decide⟩ := by
  induction n with
  | zero =>
    unfold KMor1.mult
    rw [KMor1.interp_rec1_zero, KMor1.interp_zero]
    omega
  | succ n ih =>
    unfold KMor1.mult
    rw [KMor1.interp_rec1_succ, KMor1.interp_comp, KMor1.interp_add,
        KMor1.interp_proj, KMor1.interp_proj]
    have hidx1 :
        (⟨1, by decide⟩ : Fin (1 + 1 + 1))
          = Fin.castAdd 1
              (⟨1, by decide⟩ : Fin (1 + 1)) := by
      apply Fin.ext; rfl
    rw [hidx1, Fin.append_left]
    have hidx2 :
        (⟨2, by decide⟩ : Fin (1 + 1 + 1))
          = Fin.natAdd (1 + 1) (⟨0, by decide⟩ : Fin 1) := by
      apply Fin.ext; rfl
    rw [hidx2, Fin.append_right]
    have hsucc : (⟨1, by decide⟩ : Fin (1 + 1))
        = Fin.succ (⟨0, by decide⟩ : Fin 1) := by
      apply Fin.ext; rfl
    rw [hsucc, Fin.cons_succ]
    change p ⟨0, by decide⟩ + KMor1.mult.interp (Fin.cons n p)
        = (n + 1) * p ⟨0, by decide⟩
    rw [ih, Nat.succ_mul]
    omega

/-- Interpretation of `mult`: `ctx 0 * ctx 1`. -/
@[simp] theorem KMor1.interp_mult (ctx : Fin 2 → ℕ) :
    KMor1.mult.interp ctx = ctx 0 * ctx 1 := by
  have hctx :
      ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [hctx, KMor1.mult_aux]
  rfl

example : KMor1.mult.level = 2 := by decide

/-- Helper: monus with arguments swapped, recursing on slot 0.
`monusSwapped(y, x) = x ∸ y`.  K^sim's recursion always recurses
on slot 0; this helper makes that explicit, with `KMor1.monus`
below swapping the arg order to recover the conventional
`λxy. x ∸ y`. -/
private def KMor1.monusSwapped : KMor1 2 :=
  KMor1.rec1
    (h := KMor1.proj ⟨0, by decide⟩)
    (g := KMor1.comp KMor1.pred
            (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))

private lemma KMor1.monusSwapped_aux (n : ℕ) (p : Fin 1 → ℕ) :
    KMor1.monusSwapped.interp (Fin.cons n p)
      = p ⟨0, by decide⟩ - n := by
  induction n with
  | zero =>
    unfold KMor1.monusSwapped
    rw [KMor1.interp_rec1_zero, KMor1.interp_proj]
    simp
  | succ n ih =>
    unfold KMor1.monusSwapped
    rw [KMor1.interp_rec1_succ, KMor1.interp_comp,
        KMor1.interp_pred, KMor1.interp_proj]
    have hidx :
        (⟨2, by decide⟩ : Fin (1 + 1 + 1))
          = Fin.natAdd (1 + 1) (⟨0, by decide⟩ : Fin 1) := by
      apply Fin.ext; rfl
    rw [hidx, Fin.append_right]
    change (KMor1.monusSwapped.interp (Fin.cons n p)).pred
        = p ⟨0, by decide⟩ - (n + 1)
    rw [ih, Nat.pred_eq_sub_one]
    omega

@[simp] private theorem KMor1.interp_monusSwapped
    (ctx : Fin 2 → ℕ) :
    KMor1.monusSwapped.interp ctx = ctx 1 - ctx 0 := by
  have hctx :
      ctx = Fin.cons (ctx 0) (fun j => ctx (Fin.succ j)) := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [hctx, KMor1.monusSwapped_aux]
  rfl

example : KMor1.monusSwapped.level = 2 := by decide

/-- Truncated subtraction: `monus(x, y) = x ∸ y`.

Tourlakis PR §0.1.0.17(a); Notes 10.2.12 row 6. -/
def KMor1.monus : KMor1 2 := KMor1.swap KMor1.monusSwapped

/-- Interpretation of `monus`: `ctx 0 - ctx 1` (truncated). -/
@[simp] theorem KMor1.interp_monus (ctx : Fin 2 → ℕ) :
    KMor1.monus.interp ctx = ctx 0 - ctx 1 := by
  unfold KMor1.monus
  rw [KMor1.interp_swap, KMor1.interp_monusSwapped]

example : KMor1.monus.level = 2 := by decide

/-- Binary maximum of two natural-number inputs, as a
`K^sim` morphism. Defined via truncated subtraction:
`max x y = (x ∸ y) + y`. Closed form: `(maxK).interp v =
Nat.max (v 0) (v 1)`. Level ≤ 2 (composition of
`KMor1.add` at level 1 with `KMor1.monus` at level 2 and
projections at level 0). -/
def KMor1.maxK : KMor1 2 :=
  KMor1.comp KMor1.add
    (fun i : Fin 2 =>
      match i with
      | ⟨0, _⟩ => KMor1.comp KMor1.monus (fun j : Fin 2 =>
                    match j with
                    | ⟨0, _⟩ => KMor1.proj ⟨0, by decide⟩
                    | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩)
      | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩)

/-- Interpretation of `maxK`: `Nat.max (ctx 0) (ctx 1)`. -/
@[simp] theorem KMor1.interp_maxK (v : Fin 2 → ℕ) :
    KMor1.maxK.interp v = Nat.max (v 0) (v 1) := by
  simp only [KMor1.maxK, KMor1.interp_comp,
    KMor1.interp_add, KMor1.interp_monus,
    KMor1.interp_proj]
  change v 0 - v 1 + v 1 = max (v 0) (v 1)
  omega

example : KMor1.maxK.level = 2 := by decide
theorem KMor1.maxK_level : KMor1.maxK.level ≤ 2 := by decide

/-- N-ary maximum of an input vector, as a `K^sim` morphism of
arity `a`. Recursive: `maxOver 0` is the constant-0 morphism;
`maxOver (a + 1)` takes the max of slot 0 with `maxOver a`
applied to the tail. Closed form:
`(maxOver a).interp v = Fin.maxOfNat a v`. Level ≤ 2 (composition
of `KMor1.maxK` with projections and `KMor1.zero`). -/
def KMor1.maxOver : (a : ℕ) → KMor1 a
  | 0     => KMor1.zero
  | a + 1 =>
      KMor1.comp KMor1.maxK
        (fun i : Fin 2 =>
          match i with
          | ⟨0, _⟩ => KMor1.proj ⟨0, Nat.succ_pos a⟩
          | ⟨1, _⟩ =>
              KMor1.comp (KMor1.maxOver a)
                (fun j : Fin a =>
                  KMor1.proj ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩))

/-- Interpretation of `maxOver`: `Fin.maxOfNat a v`. -/
@[simp] theorem KMor1.interp_maxOver :
    ∀ (a : ℕ) (v : Fin a → ℕ),
      (KMor1.maxOver a).interp v = Fin.maxOfNat a v := by
  intro a
  induction a with
  | zero =>
      intro v
      simp [KMor1.maxOver, KMor1.interp_zero, Fin.maxOfNat]
  | succ n ih =>
      intro v
      simp only [KMor1.maxOver, KMor1.interp_comp,
        KMor1.interp_maxK, KMor1.interp_proj]
      rw [ih]
      -- Goal: max (v 0) (Fin.maxOfNat n (v ∘ Fin.succ-like proj))
      --     = Fin.maxOfNat (n+1) v.
      -- RHS unfolds via Fin.foldr_succ to
      --     max (Fin.foldr n ... 0) (v 0).
      unfold Fin.maxOfNat
      rw [Fin.foldr_succ]
      -- Both sides now have the shape `max (v 0) (Fin.foldr n …)`
      -- vs. `max (Fin.foldr n …) (v 0)`; close via `Nat.max_comm`
      -- and reindexing of the proj-into-Fin.succ wrapper.
      apply Nat.max_comm

example : (KMor1.maxOver 4).level ≤ 2 := by decide

/-- `KMor1.maxOver a` has level ≤ 2 for every arity `a`. -/
theorem KMor1.maxOver_level :
    ∀ a, (KMor1.maxOver a).level ≤ 2 := by
  intro a
  induction a with
  | zero =>
      -- `maxOver 0 = KMor1.zero`; level 0 ≤ 2.
      change KMor1.level (KMor1.maxOver 0) ≤ 2
      unfold KMor1.maxOver
      decide
  | succ n ih =>
      change KMor1.level
          (KMor1.comp KMor1.maxK
            (fun i : Fin 2 =>
              match i with
              | ⟨0, _⟩ => KMor1.proj ⟨0, Nat.succ_pos n⟩
              | ⟨1, _⟩ =>
                  KMor1.comp (KMor1.maxOver n)
                    (fun j : Fin n =>
                      KMor1.proj ⟨j.val + 1,
                        Nat.succ_lt_succ j.isLt⟩))) ≤ 2
      unfold KMor1.level
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · exact KMor1.maxK_level
      · apply Fin.maxOfNat_le
        intro i
        match i with
        | ⟨0, _⟩ =>
            -- `proj _` always has level 0.
            change (0 : ℕ) ≤ 2
            decide
        | ⟨1, _⟩ =>
            -- inner is comp (maxOver n) (proj …); level
            --   = max ih (Fin.maxOfNat _ (proj_).level = 0).
            change KMor1.level
                (KMor1.comp (KMor1.maxOver n)
                  (fun j : Fin n =>
                    KMor1.proj
                      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)) ≤ 2
            unfold KMor1.level
            refine Nat.max_le.mpr ⟨ih, ?_⟩
            exact Fin.maxOfNat_le (fun _ => Nat.zero_le _)

/-- Sign function: `signum(0) = 0`, `signum(n+1) = 1`. Equivalent
to the level-1 composite `isZero ∘ isZero`: `isZero(n) = 1 - sgn n`,
so `isZero (isZero n) = sgn n`. Used to normalize `eq`'s {0, ≥1}-
valued output to {0, 1}.

Tourlakis PR §0.1.0.17(3) (`λx. 1 ∸ x ∈ K_1`); composition with
itself stays at K^sim_1. -/
private def KMor1.signum : KMor1 1 :=
  KMor1.comp KMor1.isZero (fun _ : Fin 1 => KMor1.isZero)

@[simp] private theorem KMor1.interp_signum (ctx : Fin 1 → ℕ) :
    KMor1.signum.interp ctx = if ctx 0 = 0 then 0 else 1 := by
  unfold KMor1.signum
  rw [KMor1.interp_comp, KMor1.interp_isZero, KMor1.interp_isZero]
  by_cases h : ctx 0 = 0
  · simp [h]
  · simp [h]

example : KMor1.signum.level = 1 := by decide

/-- Characteristic of the predicate `x = y` (Tourlakis convention):
`eq(x, y) = 0` iff `x = y`, `eq(x, y) = 1` iff `x ≠ y`.

Composes with `cond` for "if x = y then z else z'":
`cond(eq(x, y), z, z') = if x = y then z else z'`.

Construction: `signum((x ∸ y) + (y ∸ x))`. The inner sum vanishes
exactly at `x = y`; `signum` normalizes the result to {0, 1}.

Tourlakis Notes 10.2.20 (`λx.x = a ∈ K_{1,*}` for fixed `a`);
generalized here to two-variable equality via Boolean closure of
K_{n,*} (Notes 10.2.14) plus `monus` at K^sim_2. -/
def KMor1.eq : KMor1 2 :=
  KMor1.comp KMor1.signum (fun _ : Fin 1 =>
    KMor1.comp KMor1.add (fun i => match i with
      | ⟨0, _⟩ => KMor1.monus
      | ⟨1, _⟩ => KMor1.swap KMor1.monus))

@[simp] theorem KMor1.interp_eq (ctx : Fin 2 → ℕ) :
    KMor1.eq.interp ctx = if ctx 0 = ctx 1 then 0 else 1 := by
  unfold KMor1.eq
  rw [KMor1.interp_comp, KMor1.interp_signum,
      KMor1.interp_comp, KMor1.interp_add,
      KMor1.interp_monus, KMor1.interp_swap, KMor1.interp_monus]
  by_cases h : ctx 0 = ctx 1
  · simp [h]
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · have h1 : ctx 0 - ctx 1 = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
      have h2 : ctx 1 - ctx 0 > 0 := Nat.sub_pos_of_lt hlt
      simp [h, h1]
      omega
    · have h1 : ctx 1 - ctx 0 = 0 := Nat.sub_eq_zero_of_le (le_of_lt hgt)
      have h2 : ctx 0 - ctx 1 > 0 := Nat.sub_pos_of_lt hgt
      simp [h, h1]
      omega

example : KMor1.eq.level = 2 := by decide

/-- "If x = y then z else z'": composition of `cond` with
`eq(x, y)`.

`condEq(x, y, z, z') = z` when `x = y`, `z'` otherwise. -/
def KMor1.condEq : KMor1 4 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ =>
        KMor1.comp KMor1.eq (fun j => match j with
          | ⟨0, _⟩ => KMor1.proj ⟨0, by decide⟩
          | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩)
    | ⟨1, _⟩ => KMor1.proj ⟨2, by decide⟩
    | ⟨2, _⟩ => KMor1.proj ⟨3, by decide⟩)

@[simp] theorem KMor1.interp_condEq (ctx : Fin 4 → ℕ) :
    KMor1.condEq.interp ctx
      = if ctx 0 = ctx 1 then ctx 2 else ctx 3 := by
  unfold KMor1.condEq
  rw [KMor1.interp_comp, KMor1.interp_cond, KMor1.interp_comp,
      KMor1.interp_eq, KMor1.interp_proj, KMor1.interp_proj,
      KMor1.interp_proj, KMor1.interp_proj]
  by_cases h : ctx 0 = ctx 1
  · simp [h]
  · simp [h]

example : KMor1.condEq.level = 2 := by decide

/-- Powers of two: `pow2(0) = 1`, `pow2(x+1) = double(pow2(x))`.

Tourlakis PR §0.1.0.17(c); Notes 10.2.12 row 5. -/
def KMor1.pow2 : KMor1 1 :=
  KMor1.rec1
    (h := KMor1.one)
    (g := KMor1.comp KMor1.double
            (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩))

private lemma KMor1.pow2_aux (n : ℕ) :
    KMor1.pow2.interp (Fin.cons n Fin.elim0) = 2 ^ n := by
  induction n with
  | zero =>
    unfold KMor1.pow2
    rw [KMor1.interp_rec1_zero, KMor1.interp_one]
    rfl
  | succ n ih =>
    unfold KMor1.pow2
    rw [KMor1.interp_rec1_succ, KMor1.interp_comp,
        KMor1.interp_double, KMor1.interp_proj]
    have hidx :
        (⟨1, by decide⟩ : Fin (0 + 1 + 1))
          = Fin.natAdd (0 + 1) (⟨0, by decide⟩ : Fin 1) := by
      apply Fin.ext; rfl
    rw [hidx, Fin.append_right]
    change 2 * KMor1.pow2.interp (Fin.cons n Fin.elim0)
        = 2 ^ (n + 1)
    rw [ih, pow_succ]
    omega

/-- Interpretation of `pow2`: `2 ^ ctx 0`. -/
@[simp] theorem KMor1.interp_pow2 (ctx : Fin 1 → ℕ) :
    KMor1.pow2.interp ctx = 2 ^ ctx 0 := by
  have hctx : ctx = Fin.cons (ctx 0) Fin.elim0 := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
  rw [hctx]
  exact KMor1.pow2_aux (ctx 0)

example : KMor1.pow2.level = 2 := by decide

/-- `r`-fold composition of `KMor1.pow2`. `pow2_iter 0` is the
arity-1 projection at slot 0 (i.e., the identity on `ℕ`);
`pow2_iter (r + 1)` composes `KMor1.pow2` with `pow2_iter r`.
Closed form: `(pow2_iter r).interp v = tower r (v 0)`, the
height-`r` tower of twos applied to the input. Level ≤ 2. -/
def KMor1.pow2_iter : (r : ℕ) → KMor1 1
  | 0     => KMor1.proj ⟨0, by decide⟩
  | r + 1 =>
      KMor1.comp KMor1.pow2 (fun _ : Fin 1 => KMor1.pow2_iter r)

/-- Interpretation of `pow2_iter r`: `tower r (v 0)`. -/
@[simp] theorem KMor1.interp_pow2_iter :
    ∀ (r : ℕ) (v : Fin 1 → ℕ),
      (KMor1.pow2_iter r).interp v = tower r (v 0) := by
  intro r
  induction r with
  | zero =>
      intro v
      simp [KMor1.pow2_iter, KMor1.interp_proj, tower]
  | succ n ih =>
      intro v
      simp only [KMor1.pow2_iter, KMor1.interp_comp,
        KMor1.interp_pow2]
      rw [ih]
      simp [tower]

example : (KMor1.pow2_iter 3).level ≤ 2 := by decide

/-- `KMor1.pow2_iter r` has level ≤ 2 for every `r`. -/
theorem KMor1.pow2_iter_level :
    ∀ r, (KMor1.pow2_iter r).level ≤ 2 := by
  intro r
  induction r with
  | zero =>
      change KMor1.level (KMor1.pow2_iter 0) ≤ 2
      unfold KMor1.pow2_iter
      decide
  | succ n ih =>
      change KMor1.level
          (KMor1.comp KMor1.pow2
            (fun _ : Fin 1 => KMor1.pow2_iter n)) ≤ 2
      unfold KMor1.level
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · -- pow2.level = 2.
        decide
      · exact Fin.maxOfNat_le (fun _ => ih)

/-- Base family for `modAux`: `f₀(0, y) = 0`, `f₁(0, y) = pred(y)`. -/
private def KMor1.modAux_h : Fin 2 → KMor1 1 := fun i =>
  match i with
  | ⟨0, _⟩ => KMor1.zero
  | ⟨1, _⟩ => KMor1.pred

/-- Step family for `modAux` (Fin 4 step context: x, y, prev_f₀,
prev_f₁); see `modAux` docstring for slot layout. -/
private def KMor1.modAux_g : Fin 2 → KMor1 (1 + 1 + 2) := fun i =>
  match i with
  | ⟨0, _⟩ =>
      KMor1.comp KMor1.cond (fun j => match j with
        | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
        | ⟨1, _⟩ => KMor1.zero
        | ⟨2, _⟩ => KMor1.comp KMor1.succ
                      (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
  | ⟨1, _⟩ =>
      KMor1.comp KMor1.cond (fun j => match j with
        | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
        | ⟨1, _⟩ => KMor1.comp KMor1.pred
                      (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)
        | ⟨2, _⟩ => KMor1.comp KMor1.pred
                      (fun _ : Fin 1 => KMor1.proj ⟨3, by decide⟩))

/-- Helper: joint recursion of `mod` and a "distance to wrap"
companion. Output index 0 of the simrec is the `mod` component;
the second component `(y ∸ 1) ∸ mod(x, y)` is internal and used
to make the wrap test expressible at level 1 via `cond`.

At `y = 0`: `f₁` stays at `0` forever (since `pred(0) = 0`), so
`f₀(x, 0) = 0` for all `x`. The outer `KMor1.mod` (next def)
wraps this case to match `Nat.mod_zero : x % 0 = x`.

Marchenkov 2007 (placement); generalizes Tourlakis Notes 4.2.3's
two-row companion-shift technique. -/
private def KMor1.modAux : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 1) (i := ⟨0, by decide⟩)
    KMor1.modAux_h KMor1.modAux_g

example : KMor1.modAux.level = 2 := by decide

private lemma KMor1.mod_succ_wrap (x y : ℕ) (hy : 0 < y)
    (hw : x % y = y - 1) :
    (x + 1) % y = 0 := by
  have hdiv : y ∣ (x + 1) := by
    refine ⟨x / y + 1, ?_⟩
    have h := Nat.mod_add_div x y
    have hx : x = (y - 1) + y * (x / y) := by
      rw [← hw]; omega
    rw [Nat.mul_succ]
    omega
  rcases hdiv with ⟨k, hk⟩
  rw [hk, Nat.mul_mod_right]

private lemma KMor1.mod_succ_no_wrap (x y : ℕ) (hy : 0 < y)
    (hw : x % y < y - 1) :
    (x + 1) % y = x % y + 1 := by
  have hxy : x % y + 1 < y := by omega
  have h1 : x + 1 = (x % y + 1) + y * (x / y) := by
    have h := Nat.mod_add_div x y; omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hxy]

private theorem KMor1.modAux_components (x y : ℕ) :
    ∀ (j : Fin 2),
    KMor1.simrecVec KMor1.modAux_h KMor1.modAux_g
        (fun _ : Fin 1 => y) x j
      = (if y = 0 then 0
         else
           match j with
           | ⟨0, _⟩ => x % y
           | ⟨1, _⟩ => (y - 1) - x % y) := by
  induction x with
  | zero =>
    intro j
    match j with
    | ⟨0, _⟩ =>
      simp only [KMor1.simrecVec_zero, KMor1.modAux_h,
        KMor1.interp_zero]
      split_ifs with hy
      · rfl
      · simp [Nat.zero_mod]
    | ⟨1, _⟩ =>
      simp only [KMor1.simrecVec_zero, KMor1.modAux_h,
        KMor1.interp_pred]
      split_ifs with hy
      · simp [hy]
      · simp [Nat.pred_eq_sub_one, Nat.zero_mod]
  | succ x ih =>
    intro j
    have ih0 := ih ⟨0, by decide⟩
    have ih1 := ih ⟨1, by decide⟩
    match j with
    | ⟨0, _⟩ =>
      rw [KMor1.simrecVec_succ]
      change (KMor1.modAux_g ⟨0, by decide⟩).interp _ = _
      change (KMor1.comp KMor1.cond _).interp _ = _
      simp only [KMor1.interp_comp, KMor1.interp_cond,
        KMor1.interp_zero, KMor1.interp_succ,
        KMor1.interp_proj]
      have hf3 : ¬ ((3 : ℕ) < 1 + 1) := by decide
      have hf2 : ¬ ((2 : ℕ) < 1 + 1) := by decide
      simp only [hf3, hf2, dite_false]
      simp only [show (3 - (1 + 1) : ℕ) = 1 from rfl,
        show (2 - (1 + 1) : ℕ) = 0 from rfl, ih0, ih1]
      by_cases hy : y = 0
      · simp [hy]
      · simp only [hy, ite_false]
        by_cases hwrap : (y - 1) - x % y = 0
        · have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hw : x % y = y - 1 := by omega
          have hsucc : (x + 1) % y = 0 :=
            KMor1.mod_succ_wrap x y hpos hw
          simp [hwrap, hsucc]
        · simp only [hwrap, ite_false]
          have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hlt : x % y < y - 1 := by omega
          have hsucc : (x + 1) % y = x % y + 1 :=
            KMor1.mod_succ_no_wrap x y hpos hlt
          rw [hsucc]
    | ⟨1, _⟩ =>
      rw [KMor1.simrecVec_succ]
      change (KMor1.modAux_g ⟨1, by decide⟩).interp _ = _
      change (KMor1.comp KMor1.cond _).interp _ = _
      simp only [KMor1.interp_comp, KMor1.interp_cond,
        KMor1.interp_pred, KMor1.interp_proj]
      have hf3 : ¬ ((3 : ℕ) < 1 + 1) := by decide
      have ht1 : ((1 : ℕ) < 1 + 1) := by decide
      have hne : ¬ ((1 : ℕ) = 0) := by decide
      simp only [hf3, ht1, hne, dite_true, dite_false]
      simp only [show (3 - (1 + 1) : ℕ) = 1 from rfl, ih1]
      by_cases hy : y = 0
      · simp [hy, Nat.pred_eq_sub_one]
      · simp only [hy, ite_false]
        by_cases hwrap : (y - 1) - x % y = 0
        · have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hw : x % y = y - 1 := by omega
          have hsucc : (x + 1) % y = 0 :=
            KMor1.mod_succ_wrap x y hpos hw
          simp [hwrap, hsucc, Nat.pred_eq_sub_one]
        · simp only [hwrap, ite_false]
          have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hlt : x % y < y - 1 := by omega
          have hsucc : (x + 1) % y = x % y + 1 :=
            KMor1.mod_succ_no_wrap x y hpos hlt
          rw [hsucc, Nat.pred_eq_sub_one]
          omega

/-- Remainder: `mod(x, y) = x % y` matching Lean's `Nat.mod`,
including `x % 0 = x` (`Nat.mod_zero`).

Construction: `cond(y, x, modAux(x, y))`. At `y = 0` returns `x`;
at `y > 0` defers to `modAux`, which computes `x % y` via the
companion-tracked simrec.

Marchenkov 2007 (basis member, derived from `x ∸ y · (x/y)` over
the basis `{x+y, x∸y, x/y, 2^x}`); inspired by Tourlakis Notes
4.2.3's `rem(x, 2)` companion-shift technique. The convention
`rm(x, 0) = x` matches Marchenkov §1 and Lean's `Nat.mod_zero`. -/
def KMor1.mod : KMor1 2 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩
    | ⟨2, _⟩ => KMor1.modAux)

example : KMor1.mod.level = 2 := by decide

/-- Interpretation of `mod`: `ctx 0 % ctx 1` (matches `Nat.mod`). -/
@[simp] theorem KMor1.interp_mod (ctx : Fin 2 → ℕ) :
    KMor1.mod.interp ctx = ctx 0 % ctx 1 := by
  unfold KMor1.mod
  rw [KMor1.interp_comp, KMor1.interp_cond]
  change (if (KMor1.proj (⟨1, by decide⟩ : Fin 2)).interp ctx = 0
          then (KMor1.proj (⟨0, by decide⟩ : Fin 2)).interp ctx
          else KMor1.modAux.interp ctx) = ctx 0 % ctx 1
  rw [KMor1.interp_proj, KMor1.interp_proj]
  by_cases hy : ctx 1 = 0
  · have hctx1 : ctx (⟨1, by decide⟩ : Fin 2) = 0 := hy
    rw [if_pos hctx1, hy, Nat.mod_zero]
    rfl
  · have hctx1 : ¬ ctx (⟨1, by decide⟩ : Fin 2) = 0 := hy
    rw [if_neg hctx1]
    unfold KMor1.modAux
    rw [KMor1.interp_simrec]
    have hparams :
        (fun j : Fin 1 => ctx (Fin.succ j)) = (fun _ : Fin 1 => ctx 1) := by
      funext j
      match j with
      | ⟨0, _⟩ => rfl
    rw [hparams]
    rw [KMor1.modAux_components (ctx 0) (ctx 1) ⟨0, by decide⟩]
    simp only [hy, ite_false]

/-- Base family for `divAux`: `f₀(0,y)=0, f₁(0,y)=pred(y),
f₂(0,y)=0`. -/
private def KMor1.divAux_h : Fin 3 → KMor1 1 := fun i =>
  match i with
  | ⟨0, _⟩ => KMor1.zero
  | ⟨1, _⟩ => KMor1.pred
  | ⟨2, _⟩ => KMor1.zero

/-- Step family for `divAux` (Fin 5 step context: x, y,
prev_f₀, prev_f₁, prev_f₂); see `divAux` docstring for slot
layout. -/
private def KMor1.divAux_g : Fin 3 → KMor1 (1 + 1 + 3) := fun i =>
  match i with
  | ⟨0, _⟩ =>
      KMor1.comp KMor1.cond (fun j => match j with
        | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
        | ⟨1, _⟩ => KMor1.zero
        | ⟨2, _⟩ => KMor1.comp KMor1.succ
                      (fun _ : Fin 1 => KMor1.proj ⟨2, by decide⟩))
  | ⟨1, _⟩ =>
      KMor1.comp KMor1.cond (fun j => match j with
        | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
        | ⟨1, _⟩ => KMor1.comp KMor1.pred
                      (fun _ : Fin 1 => KMor1.proj ⟨1, by decide⟩)
        | ⟨2, _⟩ => KMor1.comp KMor1.pred
                      (fun _ : Fin 1 => KMor1.proj ⟨3, by decide⟩))
  | ⟨2, _⟩ =>
      KMor1.comp KMor1.cond (fun j => match j with
        | ⟨0, _⟩ => KMor1.proj ⟨3, by decide⟩
        | ⟨1, _⟩ => KMor1.comp KMor1.succ
                      (fun _ : Fin 1 => KMor1.proj ⟨4, by decide⟩)
        | ⟨2, _⟩ => KMor1.proj ⟨4, by decide⟩)

/-- Helper: joint recursion of `mod`, "distance to wrap", and
`div`. Output index 2 of the simrec (the `div` component).

The first two components mirror `modAux`; the third tracks the
running quotient, incrementing exactly at wrap points (when
`prev_f₁ = 0`, i.e. `x % y = y - 1`).

At `y = 0`: `f₁` stays at 0 forever, so the cond switch always
selects `branch1 = succ(prev_f₂)`; hence `f₂(x, 0) = x`,
matching Marchenkov §1's convention `x/0 = x`.

Marchenkov 2007 (`x/y` is one of the four basis elements
`S = {x+y, x∸y, x/y, 2^x}`); construction technique extends
Tourlakis Notes 4.2.3's two-row companion-shift to a three-row
shift-plus-counter. -/
private def KMor1.divAux : KMor1 2 :=
  KMor1.simrec (a := 1) (k := 2) (i := ⟨2, by decide⟩)
    KMor1.divAux_h KMor1.divAux_g

example : KMor1.divAux.level = 2 := by decide

private lemma KMor1.div_succ_wrap (x y : ℕ) (hy : 0 < y)
    (hw : x % y = y - 1) :
    (x + 1) / y = x / y + 1 := by
  have hdvd : y ∣ (x + 1) := by
    refine ⟨x / y + 1, ?_⟩
    have h := Nat.mod_add_div x y
    rw [hw] at h
    rw [Nat.mul_succ]
    omega
  rcases hdvd with ⟨k, hk⟩
  rw [hk, Nat.mul_div_cancel_left _ hy]
  have hkeq : y * (x / y + 1) = y * k := by
    rw [Nat.mul_succ]
    have h := Nat.mod_add_div x y
    rw [hw] at h
    omega
  exact (Nat.eq_of_mul_eq_mul_left hy hkeq).symm

private lemma KMor1.div_succ_no_wrap (x y : ℕ) (hy : 0 < y)
    (hw : x % y < y - 1) :
    (x + 1) / y = x / y := by
  have hmod_eq : (x + 1) % y = x % y + 1 :=
    KMor1.mod_succ_no_wrap x y hy hw
  have h1 := Nat.mod_add_div x y
  have h2 := Nat.mod_add_div (x + 1) y
  rw [hmod_eq] at h2
  have hmul : y * ((x + 1) / y) = y * (x / y) := by omega
  exact Nat.eq_of_mul_eq_mul_left hy hmul

private theorem KMor1.divAux_components (x y : ℕ) :
    ∀ (j : Fin 3),
    KMor1.simrecVec KMor1.divAux_h KMor1.divAux_g
        (fun _ : Fin 1 => y) x j
      = (if y = 0 then
           match j with
           | ⟨0, _⟩ => 0
           | ⟨1, _⟩ => 0
           | ⟨2, _⟩ => x
         else
           match j with
           | ⟨0, _⟩ => x % y
           | ⟨1, _⟩ => (y - 1) - x % y
           | ⟨2, _⟩ => x / y) := by
  induction x with
  | zero =>
    intro j
    match j with
    | ⟨0, _⟩ =>
      simp only [KMor1.simrecVec_zero, KMor1.divAux_h,
        KMor1.interp_zero]
      split_ifs with hy
      · rfl
      · simp [Nat.zero_mod]
    | ⟨1, _⟩ =>
      simp only [KMor1.simrecVec_zero, KMor1.divAux_h,
        KMor1.interp_pred]
      split_ifs with hy
      · simp [hy]
      · simp [Nat.pred_eq_sub_one, Nat.zero_mod]
    | ⟨2, _⟩ =>
      simp only [KMor1.simrecVec_zero, KMor1.divAux_h,
        KMor1.interp_zero]
      split_ifs with hy
      · rfl
      · simp [Nat.zero_div]
  | succ x ih =>
    intro j
    have ih0 := ih ⟨0, by decide⟩
    have ih1 := ih ⟨1, by decide⟩
    have ih2 := ih ⟨2, by decide⟩
    match j with
    | ⟨0, _⟩ =>
      rw [KMor1.simrecVec_succ]
      change (KMor1.divAux_g ⟨0, by decide⟩).interp _ = _
      change (KMor1.comp KMor1.cond _).interp _ = _
      simp only [KMor1.interp_comp, KMor1.interp_cond,
        KMor1.interp_zero, KMor1.interp_succ,
        KMor1.interp_proj]
      have hf3 : ¬ ((3 : ℕ) < 1 + 1) := by decide
      have hf2 : ¬ ((2 : ℕ) < 1 + 1) := by decide
      simp only [hf3, hf2, dite_false]
      simp only [show (3 - (1 + 1) : ℕ) = 1 from rfl,
        show (2 - (1 + 1) : ℕ) = 0 from rfl, ih0, ih1]
      by_cases hy : y = 0
      · simp [hy]
      · simp only [hy, ite_false]
        by_cases hwrap : (y - 1) - x % y = 0
        · have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hw : x % y = y - 1 := by omega
          have hsucc : (x + 1) % y = 0 :=
            KMor1.mod_succ_wrap x y hpos hw
          simp [hwrap, hsucc]
        · simp only [hwrap, ite_false]
          have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hlt : x % y < y - 1 := by omega
          have hsucc : (x + 1) % y = x % y + 1 :=
            KMor1.mod_succ_no_wrap x y hpos hlt
          rw [hsucc]
    | ⟨1, _⟩ =>
      rw [KMor1.simrecVec_succ]
      change (KMor1.divAux_g ⟨1, by decide⟩).interp _ = _
      change (KMor1.comp KMor1.cond _).interp _ = _
      simp only [KMor1.interp_comp, KMor1.interp_cond,
        KMor1.interp_pred, KMor1.interp_proj]
      have hf3 : ¬ ((3 : ℕ) < 1 + 1) := by decide
      have ht1 : ((1 : ℕ) < 1 + 1) := by decide
      have hne : ¬ ((1 : ℕ) = 0) := by decide
      simp only [hf3, ht1, hne, dite_true, dite_false]
      simp only [show (3 - (1 + 1) : ℕ) = 1 from rfl, ih1]
      by_cases hy : y = 0
      · simp [hy, Nat.pred_eq_sub_one]
      · simp only [hy, ite_false]
        by_cases hwrap : (y - 1) - x % y = 0
        · have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hw : x % y = y - 1 := by omega
          have hsucc : (x + 1) % y = 0 :=
            KMor1.mod_succ_wrap x y hpos hw
          simp [hwrap, hsucc, Nat.pred_eq_sub_one]
        · simp only [hwrap, ite_false]
          have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hlt : x % y < y - 1 := by omega
          have hsucc : (x + 1) % y = x % y + 1 :=
            KMor1.mod_succ_no_wrap x y hpos hlt
          rw [hsucc, Nat.pred_eq_sub_one]
          omega
    | ⟨2, _⟩ =>
      rw [KMor1.simrecVec_succ]
      change (KMor1.divAux_g ⟨2, by decide⟩).interp _ = _
      change (KMor1.comp KMor1.cond _).interp _ = _
      simp only [KMor1.interp_comp, KMor1.interp_cond,
        KMor1.interp_succ, KMor1.interp_proj]
      have hf3 : ¬ ((3 : ℕ) < 1 + 1) := by decide
      have hf4 : ¬ ((4 : ℕ) < 1 + 1) := by decide
      simp only [hf3, hf4, dite_false]
      simp only [show (3 - (1 + 1) : ℕ) = 1 from rfl,
        show (4 - (1 + 1) : ℕ) = 2 from rfl, ih1, ih2]
      by_cases hy : y = 0
      · simp [hy]
      · simp only [hy, ite_false]
        by_cases hwrap : (y - 1) - x % y = 0
        · have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hw : x % y = y - 1 := by omega
          have hsucc : (x + 1) / y = x / y + 1 :=
            KMor1.div_succ_wrap x y hpos hw
          simp [hwrap, hsucc]
        · simp only [hwrap, ite_false]
          have hpos : 0 < y := Nat.pos_of_ne_zero hy
          have hxy : x % y < y := Nat.mod_lt _ hpos
          have hlt : x % y < y - 1 := by omega
          have hsucc : (x + 1) / y = x / y :=
            KMor1.div_succ_no_wrap x y hpos hlt
          rw [hsucc]

/-- Integer division (Marchenkov convention): `div(x, y) = ⌊x/y⌋`
for `y ≥ 1`; `div(x, 0) = x` per Marchenkov 2007 §1. -/
def KMor1.div : KMor1 2 := KMor1.divAux

/-- Interpretation of `div`: matches Marchenkov's `x/y` (with
`x/0 = x`). -/
@[simp] theorem KMor1.interp_div (ctx : Fin 2 → ℕ) :
    KMor1.div.interp ctx =
      if ctx 1 = 0 then ctx 0 else ctx 0 / ctx 1 := by
  unfold KMor1.div KMor1.divAux
  rw [KMor1.interp_simrec]
  have hparams :
      (fun j : Fin 1 => ctx (Fin.succ j))
        = (fun _ : Fin 1 => ctx 1) := by
    funext j
    match j with
    | ⟨0, _⟩ => rfl
  rw [hparams]
  rw [KMor1.divAux_components (ctx 0) (ctx 1) ⟨2, by decide⟩]

example : KMor1.div.level = 2 := by decide

/-- Lean-`Nat.div`-convention integer division:
`divNat(x, 0) = 0` (matching `Nat.div_zero`). Wraps `KMor1.div`
(Marchenkov 2007 §1) with an outer `cond` to short-circuit the
`y = 0` case to `0`. Lean-specific wrapper, not part of
Marchenkov's basis. -/
def KMor1.divNat : KMor1 2 :=
  KMor1.comp KMor1.cond (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
    | ⟨1, _⟩ => KMor1.zero
    | ⟨2, _⟩ => KMor1.div)

@[simp] theorem KMor1.interp_divNat (ctx : Fin 2 → ℕ) :
    KMor1.divNat.interp ctx = ctx 0 / ctx 1 := by
  unfold KMor1.divNat
  rw [KMor1.interp_comp, KMor1.interp_cond]
  change (if (KMor1.proj (⟨1, by decide⟩ : Fin 2)).interp ctx = 0
          then (KMor1.zero (n := 2)).interp ctx
          else KMor1.div.interp ctx) = ctx 0 / ctx 1
  rw [KMor1.interp_proj, KMor1.interp_zero, KMor1.interp_div]
  by_cases hy : ctx 1 = 0
  · have hctx1 : ctx (⟨1, by decide⟩ : Fin 2) = 0 := hy
    rw [if_pos hctx1, hy, Nat.div_zero]
  · have hctx1 : ¬ ctx (⟨1, by decide⟩ : Fin 2) = 0 := hy
    rw [if_neg hctx1, if_neg hy]

example : KMor1.divNat.level = 2 := by decide

/-- Bound used in the Wikipedia/Marchenkov formula for `x^y`:
`x^y + x < 2^(x*y + x + 1)`. -/
private theorem KMor1.pow_bound (x y : ℕ) :
    x ^ y + x < 2 ^ (x * y + x + 1) := by
  induction y with
  | zero =>
    have hx : x < 2 ^ x := Nat.lt_two_pow_self
    have h_pow : 2 ^ x ≥ 1 := Nat.one_le_two_pow
    have h1 : 1 + x < 2 ^ (x + 1) := by
      rw [Nat.pow_succ]
      omega
    simpa [Nat.pow_zero, Nat.mul_zero] using h1
  | succ y ih =>
    by_cases hx : x = 0
    · simp [hx,
            Nat.zero_pow (Nat.pos_of_ne_zero (Nat.succ_ne_zero y))]
    · have hx1 : x ≥ 1 := Nat.one_le_iff_ne_zero.mpr hx
      have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
      have h_2pow_pos : 2 ^ (x * y + x + 1) > 0 := Nat.two_pow_pos _
      have h_target : 2 ^ (x * (y + 1) + x + 1)
          = 2 ^ x * 2 ^ (x * y + x + 1) := by
        rw [← Nat.pow_add]
        congr 1
        rw [Nat.mul_succ]
        omega
      rw [Nat.pow_succ x y, h_target]
      have h_xy_lt : x ^ y < 2 ^ (x * y + x + 1) := by omega
      have h_xy_le : x ^ y ≤ 2 ^ (x * y + x + 1) - 1 := by omega
      have h_xy_x : x ^ y * x + x ≤ x * 2 ^ (x * y + x + 1) := by
        have h1 : x ^ y * x ≤ (2 ^ (x * y + x + 1) - 1) * x :=
          Nat.mul_le_mul_right x h_xy_le
        have h2 : (2 ^ (x * y + x + 1) - 1) * x
                  = 2 ^ (x * y + x + 1) * x - x := by
          rw [Nat.sub_mul, Nat.one_mul]
        have h3 : x ≤ 2 ^ (x * y + x + 1) * x := by
          have hge : 1 ≤ 2 ^ (x * y + x + 1) := h_2pow_pos
          calc x = 1 * x := by rw [Nat.one_mul]
            _ ≤ 2 ^ (x * y + x + 1) * x := Nat.mul_le_mul_right x hge
        rw [Nat.mul_comm x (2 ^ (x * y + x + 1))]
        omega
      have h_right :
          x * 2 ^ (x * y + x + 1) < 2 ^ x * 2 ^ (x * y + x + 1) :=
        (Nat.mul_lt_mul_right h_2pow_pos).mpr hx_lt
      omega

/-- Wikipedia/Marchenkov formula for `x^y`:

  `x^y = 2^((x*y + x + 1) * y) % (2^(x*y + x + 1) - x)`. -/
private theorem KMor1.pow_formula (x y : ℕ) :
    x ^ y =
      2 ^ ((x * y + x + 1) * y) %
        (2 ^ (x * y + x + 1) - x) := by
  have h_bound : x ^ y + x < 2 ^ (x * y + x + 1) :=
    KMor1.pow_bound x y
  have h_pow_gt_x : 2 ^ (x * y + x + 1) > x := by omega
  have hM_pos : 2 ^ (x * y + x + 1) - x > 0 := by omega
  have h_pow_mul :
      2 ^ ((x * y + x + 1) * y) = (2 ^ (x * y + x + 1)) ^ y := by
    rw [← Nat.pow_mul]
  have h_x_lt_M : x ^ y < 2 ^ (x * y + x + 1) - x := by omega
  have h_x_lt_M_base : x < 2 ^ (x * y + x + 1) - x := by
    by_cases hy : y = 0
    · subst hy
      have hx_lt : x < 2 ^ x := Nat.lt_two_pow_self
      have h_pow : 2 ^ (x * 0 + x + 1) = 2 * 2 ^ x := by
        rw [Nat.mul_zero, Nat.zero_add, Nat.pow_succ, Nat.mul_comm]
      rw [h_pow]
      omega
    · have hy1 : y ≥ 1 := Nat.one_le_iff_ne_zero.mpr hy
      have h_x_le_xy : x ≤ x ^ y := by
        by_cases hx0 : x = 0
        · simp [hx0, Nat.zero_pow (Nat.pos_of_ne_zero hy)]
        · calc x = x ^ 1 := (pow_one x).symm
            _ ≤ x ^ y := Nat.pow_le_pow_right
                (Nat.one_le_iff_ne_zero.mpr hx0) hy1
      omega
  have h_2pow_mod :
      2 ^ (x * y + x + 1) % (2 ^ (x * y + x + 1) - x) = x := by
    have h_eq : 2 ^ (x * y + x + 1)
        = x + (2 ^ (x * y + x + 1) - x) := by omega
    nth_rw 1 [h_eq]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt h_x_lt_M_base]
  have h_pow_mod :
      (2 ^ (x * y + x + 1)) ^ y % (2 ^ (x * y + x + 1) - x)
        = x ^ y % (2 ^ (x * y + x + 1) - x) := by
    conv_lhs => rw [Nat.pow_mod, h_2pow_mod]
  have h_xy_mod :
      x ^ y % (2 ^ (x * y + x + 1) - x) = x ^ y :=
    Nat.mod_eq_of_lt h_x_lt_M
  rw [h_pow_mul, h_pow_mod, h_xy_mod]

/-- Exponentiation `pow(x, y) = x ^ y` at K^sim_2.

Construction follows the Marchenkov / Wikipedia formula
`x^y = 2^((xy + x + 1) · y) mod (2^(xy + x + 1) ∸ x)`. All
sub-expressions use existing KArith functions at K^sim_2 or below;
the composition stays at K^sim_2.

Marchenkov 2007 §1: `x^y` is in the elementary class generated by
`{x+y, x∸y, x/y, 2^x}`. -/
def KMor1.pow : KMor1 2 :=
  let mTerm : KMor1 2 :=
    KMor1.comp KMor1.succ (fun _ : Fin 1 =>
      KMor1.comp KMor1.add (fun i => match i with
        | ⟨0, _⟩ => KMor1.mult
        | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩))
  let numerator : KMor1 2 :=
    KMor1.comp KMor1.pow2 (fun _ : Fin 1 =>
      KMor1.comp KMor1.mult (fun i => match i with
        | ⟨0, _⟩ => mTerm
        | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩))
  let divisor : KMor1 2 :=
    KMor1.comp KMor1.monus (fun i => match i with
      | ⟨0, _⟩ => KMor1.comp KMor1.pow2
                    (fun _ : Fin 1 => mTerm)
      | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)
  KMor1.comp KMor1.mod (fun i => match i with
    | ⟨0, _⟩ => numerator
    | ⟨1, _⟩ => divisor)

@[simp] theorem KMor1.interp_pow (ctx : Fin 2 → ℕ) :
    KMor1.pow.interp ctx = ctx 0 ^ ctx 1 := by
  unfold KMor1.pow
  simp only [KMor1.interp_comp, KMor1.interp_mod,
             KMor1.interp_pow2, KMor1.interp_mult,
             KMor1.interp_add, KMor1.interp_succ,
             KMor1.interp_monus, KMor1.interp_proj]
  exact (KMor1.pow_formula (ctx 0) (ctx 1)).symm

example : KMor1.pow.level ≤ 2 := by decide

end GebLean
