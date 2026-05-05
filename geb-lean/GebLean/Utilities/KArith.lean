import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp

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
def KMor1.monus : KMor1 2 :=
  KMor1.comp KMor1.monusSwapped (fun i => match i with
    | ⟨0, _⟩ => KMor1.proj ⟨1, by decide⟩
    | ⟨1, _⟩ => KMor1.proj ⟨0, by decide⟩)

/-- Interpretation of `monus`: `ctx 0 - ctx 1` (truncated). -/
@[simp] theorem KMor1.interp_monus (ctx : Fin 2 → ℕ) :
    KMor1.monus.interp ctx = ctx 0 - ctx 1 := by
  unfold KMor1.monus
  rw [KMor1.interp_comp, KMor1.interp_monusSwapped]
  rfl

example : KMor1.monus.level = 2 := by decide

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

end GebLean
