/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Combinators

set_option doc.verso true in
/-!
# Kristiansen's word algebra

The algebra of \[Kristiansen2005\] § 4 consists of constants and projections,
closed under composition and simultaneous recursion on notation. It is the
fragment of {name}`Geb.SizeBounded.SOf` without size-bounded successors.

## Main definitions

* {lit}`Allowed` excludes successor nodes throughout an expression.
* {lit}`LOf` consists of expressions of a given arity in the fragment.
* {lit}`constOf`, {lit}`projOf`, {lit}`compOf`, and {lit}`srnOf` are its constructors.

## Main statements

The constructor equations identify the interpretation with the paper's schemes.

## Implementation notes

The expression representation, arity checking, and interpretation are inherited
from the slice W-type of {name}`Geb.SizeBounded.sig`. The predicate restricts
syntax, without imposing a semantic resource bound. Constants at arbitrary arity
abbreviate composition with the paper's nullary constants. Recursion uses slot
zero, followed by parameters; a step receives the suffix, recursive values, and
parameters, in that order.

## References

* \[Kristiansen2005\]

## Tags

function algebra, simultaneous recursion on notation, bitstring, logspace
-/

set_option doc.verso true

namespace Geb.Kristiansen

open SizeBounded (Shape Direction sig)

public section

/-- Membership of a node in the signature: the size-bounded successor is excluded. -/
@[expose] def AllowedShape : Shape → Prop
  | .sbs _ => False
  | _ => True

/-- Every node uses a constant, projection, composition, or simultaneous recursion. -/
@[expose] def Allowed : sig.toPFunctor.W → Prop :=
  WType.elim Prop fun x ↦ AllowedShape x.1 ∧ ∀ d, x.2 d

/-- Expressions of the word algebra of \[Kristiansen2005\] at arity {lit}`n`. -/
@[expose] def LOf (n : ℕ) : Type := { e : SizeBounded.SOf n // Allowed e.1.1 }

/-- The binary-word interpretation, inherited from the containing algebra. -/
@[expose] def LOf.sem {n : ℕ} (e : LOf n) : Cobham.Sem n := e.1.sem

/-- A constant word, with unused arguments admitted by nullary composition. -/
@[expose] def constOf (n : ℕ) (w : List Bool) : LOf n :=
  ⟨SizeBounded.constOf n w, trivial, fun i ↦ i.elim0⟩

/-- The projection onto argument {lit}`i`. -/
@[expose] def projOf (n : ℕ) (i : Fin n) : LOf n :=
  ⟨SizeBounded.projOf n i, trivial, fun j ↦ j.elim0⟩

/-- Composition of expressions in the fragment. -/
@[expose] def compOf {n m : ℕ} (h : LOf m) (g : Fin m → LOf n) : LOf n :=
  ⟨SizeBounded.compOf h.1 (fun i ↦ (g i).1), trivial,
    fun d ↦ match d with
    | .inl () => h.2
    | .inr i => (g i).2⟩

/-- Component {lit}`j` of simultaneous recursion on notation. -/
@[expose] def srnOf {a b : ℕ} (g : Fin b → LOf a)
    (h : Bool → Fin b → LOf (b + a + 1)) (j : Fin b) : LOf (a + 1) :=
  ⟨SizeBounded.srnOf (fun l ↦ (g l).1) (fun i l ↦ (h i l).1) j, trivial,
    fun d ↦ match d with
    | .inl l => (g l).2
    | .inr (.inl l) => (h false l).2
    | .inr (.inr l) => (h true l).2⟩

/-- A constant's value. -/
theorem sem_constOf (n : ℕ) (w : List Bool) (x : Fin n → List Bool) :
    (constOf n w).sem x = w := rfl

/-- A projection's value. -/
theorem sem_projOf (n : ℕ) (i : Fin n) (x : Fin n → List Bool) :
    (projOf n i).sem x = x i := rfl

/-- Composition's value. -/
theorem sem_compOf {n m : ℕ} (h : LOf m) (g : Fin m → LOf n) (x : Fin n → List Bool) :
    (compOf h g).sem x = h.sem (fun i ↦ (g i).sem x) := rfl

/-- The recursion scheme as a fold on words. -/
theorem sem_srnOf {a b : ℕ} (g : Fin b → LOf a)
    (h : Bool → Fin b → LOf (b + a + 1)) (j : Fin b) (x : Fin (a + 1) → List Bool) :
    (srnOf g h j).sem x =
      SizeBounded.evalSRN (fun l ↦ (g l).sem) (fun i l ↦ (h i l).sem) (x 0) j (Fin.tail x) :=
  SizeBounded.sem_srnOf _ _ _ _

/-- On the empty recursion argument, a component is its base function. -/
theorem sem_srnOf_nil {a b : ℕ} (g : Fin b → LOf a)
    (h : Bool → Fin b → LOf (b + a + 1)) (j : Fin b) (x : Fin a → List Bool) :
    (srnOf g h j).sem (Fin.cons [] x) = (g j).sem x := rfl

/-- On a nonempty argument, all components at its tail enter the selected step. -/
theorem sem_srnOf_cons {a b : ℕ} (g : Fin b → LOf a)
    (h : Bool → Fin b → LOf (b + a + 1)) (j : Fin b) (i : Bool) (v : List Bool)
    (x : Fin a → List Bool) :
    (srnOf g h j).sem (Fin.cons (i :: v) x) =
      (h i j).sem (SizeBounded.stepEnv v (fun l ↦ (srnOf g h l).sem (Fin.cons v x)) x) :=
  SizeBounded.sem_srnOf_cons _ _ _ _ _ _

end

end Geb.Kristiansen
