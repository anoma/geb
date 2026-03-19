import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Comonad Bar Resolution

For a comonad `G` on a category `C` and an object
`X : C`, the bar resolution `B_•(G, X)` is a
simplicial object with `B_n = G^{n+1}(X)`.  Face maps
apply the counit `ε` at successive depths, and
degeneracy maps apply the comultiplication `δ`.  The
simplicial identities follow from the comonad laws.
-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace Comonad

variable (G : Comonad C) (X : C)

/--
Iterated application of a comonad's underlying
endofunctor: `iterateObj G X n = G^n(X)`.
-/
def iterateObj : ℕ → C
  | 0 => X
  | n + 1 => G.toFunctor.obj (iterateObj n)

@[simp]
lemma iterateObj_zero :
    iterateObj G X 0 = X :=
  rfl

@[simp]
lemma iterateObj_succ (n : ℕ) :
    iterateObj G X (n + 1) =
      G.toFunctor.obj (iterateObj G X n) :=
  rfl

variable {X} {Y : C}

/--
Functoriality of iterated comonad application in the
object argument: given `f : X ⟶ Y`, produce
`G^n(f) : G^n(X) ⟶ G^n(Y)`.
-/
def iterateMap (f : X ⟶ Y) : (n : ℕ) →
    iterateObj G X n ⟶ iterateObj G Y n
  | 0 => f
  | n + 1 => G.toFunctor.map (iterateMap f n)

@[simp]
lemma iterateMap_zero (f : X ⟶ Y) :
    iterateMap G f 0 = f :=
  rfl

@[simp]
lemma iterateMap_succ (f : X ⟶ Y) (n : ℕ) :
    iterateMap G f (n + 1) =
      G.toFunctor.map (iterateMap G f n) :=
  rfl

variable (X)

/--
Face map for the bar resolution at depth `i`.
Applies the counit `ε` at the `i`-th position in
`G^{n+2}(X)`, producing `G^{n+1}(X)`.

The bar resolution level `n` is
`iterateObj G X (n + 1)`.
-/
def barFace :
    (n : ℕ) → Fin (n + 2) →
      (iterateObj G X (n + 2) ⟶
        iterateObj G X (n + 1))
  | _, ⟨0, _⟩ =>
    G.ε.app (iterateObj G X _)
  | 0, ⟨_ + 1, _⟩ =>
    G.toFunctor.map
      (G.ε.app (iterateObj G X 0))
  | n + 1, ⟨i + 1, hi⟩ =>
    G.toFunctor.map
      (barFace n
        ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/--
Degeneracy map for the bar resolution at depth `i`.
Applies the comultiplication `δ` at the `i`-th
position in `G^{n+1}(X)`, producing `G^{n+2}(X)`.
-/
def barDegen :
    (n : ℕ) → Fin (n + 1) →
      (iterateObj G X (n + 1) ⟶
        iterateObj G X (n + 2))
  | _, ⟨0, _⟩ =>
    G.δ.app (iterateObj G X _)
  | n + 1, ⟨i + 1, hi⟩ =>
    G.toFunctor.map
      (barDegen n
        ⟨i, Nat.lt_of_succ_lt_succ hi⟩)

/-! ### Simplicial identities -/

lemma barFace_zero (n : ℕ) :
    barFace G X n ⟨0, Nat.zero_lt_succ _⟩ =
      G.ε.app (iterateObj G X (n + 1)) :=
  by cases n <;> rfl

lemma barDegen_zero (n : ℕ) :
    barDegen G X n ⟨0, Nat.zero_lt_succ _⟩ =
      G.δ.app (iterateObj G X n) :=
  by cases n <;> rfl

lemma barFace_succ (n : ℕ)
    (i : ℕ) (hi : i + 1 < n + 1 + 2) :
    barFace G X (n + 1)
      ⟨i + 1, hi⟩ =
      G.toFunctor.map
        (barFace G X n
          ⟨i, by omega⟩) := by
  rfl

lemma barDegen_succ (n : ℕ)
    (i : ℕ) (hi : i + 1 < n + 1 + 1) :
    barDegen G X (n + 1)
      ⟨i + 1, hi⟩ =
      G.toFunctor.map
        (barDegen G X n
          ⟨i, by omega⟩) := by
  rfl

lemma barFace_comp_barFace (n : ℕ)
    (i j : ℕ) (hij : i ≤ j)
    (hi : i < n + 2) (hj : j < n + 2) :
    barFace G X (n + 1) ⟨j + 1, by omega⟩ ≫
      barFace G X n ⟨i, hi⟩ =
    barFace G X (n + 1) ⟨i, by omega⟩ ≫
      barFace G X n ⟨j, hj⟩ := by
  induction n generalizing i j with
  | zero =>
    cases i with
    | zero =>
      erw [barFace_succ, barFace_zero,
        barFace_zero]
      exact @Comonad.counit_naturality C _ G
        (iterateObj G X 2) (iterateObj G X 1)
        (barFace G X 0 ⟨j, hj⟩)
    | succ i =>
      have : i = 0 := by omega
      have : j = 1 := by omega
      subst_vars
      erw [barFace_succ, barFace_succ,
        ← G.toFunctor.map_comp,
        ← G.toFunctor.map_comp]
      congr 1
      exact @Comonad.counit_naturality C _ G
        (iterateObj G X 1)
        (iterateObj G X 0)
        (G.ε.app X)
  | succ n ih =>
    cases i with
    | zero =>
      erw [barFace_succ, barFace_zero,
        barFace_zero]
      exact @Comonad.counit_naturality C _ G
        (iterateObj G X (n + 3))
        (iterateObj G X (n + 2))
        (barFace G X (n + 1) ⟨j, hj⟩)
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        erw [barFace_succ, barFace_succ,
          barFace_succ, barFace_succ,
          ← G.toFunctor.map_comp,
          ← G.toFunctor.map_comp]
        congr 1
        exact ih i j (by omega)
          (by omega) (by omega)

end Comonad

end CategoryTheory
