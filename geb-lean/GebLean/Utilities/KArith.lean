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

end GebLean
