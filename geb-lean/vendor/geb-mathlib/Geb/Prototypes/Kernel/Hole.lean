/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Subst

set_option doc.verso true in
/-!
# Filling a contextual hole

A sketch with one hole of type {lit}`A` in context {lit}`Γ` is an ordinary kernel term
in context {lit}`A :: Γ`. The innermost free variable represents the hole, including
its occurrences under binders. A proposed filling is a term of type {lit}`A` in
{lit}`Γ`. Checking both terms and applying {name}`Geb.Kernel.subst` fills every
occurrence without capturing variables.

The denotation is composition with the environment map {lit}`e ↦ (fu e, e)`, where
{lit}`fu` denotes the filling. This is precisely the substitution theorem
{name}`Geb.Kernel.infer_subst`. The operation checks a proposed filling; finding one
and assigning source names and locations to holes belong to the authoring tools.
The globals and context have the same interpretation as in {name}`Geb.Kernel.infer`.

## Main definitions

* {lit}`fillHole` checks a sketch and a filling, returning the substituted term.

## Main statements

* {lit}`fillHole_of_infer` accepts a well-typed sketch and filling.
* {lit}`infer_fillHole` gives the type and denotation of every accepted result.

## Tags

contextual hole, substitution, kernel, denotational semantics
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

open scoped FinEnum

/-- Fill the innermost free variable of a sketch, checking its expected type, the filling
in the surrounding context, and the sketch in the context extended by the hole. -/
def fillHole (G : List Glob) (Γ : Ctx) (A sketch filling : Tree) : Option Tree := do
  if !Ty.IsTy A then none else do
    let u ← infer G Γ filling
    if u.1 = A then do
      let _ ← infer G (A :: Γ) sketch
      some (subst filling sketch)
    else none

/-- A well-typed sketch and filling pass the checks. -/
theorem fillHole_of_infer {G : List Glob} {Γ : Ctx} {A sketch filling : Tree}
    {fu : Γ.den → Ty.den A} {m : Meaning (A :: Γ)} (hA : Ty.IsTy A = true)
    (hu : infer G Γ filling = some ⟨A, fu⟩) (ht : infer G (A :: Γ) sketch = some m) :
    fillHole G Γ A sketch filling = some (subst filling sketch) := by
  simp [fillHole, hA, hu, ht]

/-- Every accepted result has the sketch's type and denotes the sketch evaluated with
the filling's value in the hole. -/
theorem infer_fillHole {G : List Glob} {Γ : Ctx} {A sketch filling result : Tree}
    (h : fillHole G Γ A sketch filling = some result) :
    ∃ (fu : Γ.den → Ty.den A) (m : Meaning (A :: Γ)),
      infer G Γ filling = some ⟨A, fu⟩ ∧ infer G (A :: Γ) sketch = some m ∧
        infer G Γ result = some ⟨m.1, fun e ↦ m.2 (fu e, e)⟩ := by
  unfold fillHole at h
  split at h
  · cases h
  · cases hu : infer G Γ filling with
    | none => simp [hu] at h
    | some u =>
      rcases u with ⟨B, fu⟩
      simp only [hu] at h
      dsimp at h
      split at h
      · rename_i hB
        subst B
        cases ht : infer G (A :: Γ) sketch with
        | none => simp [ht] at h
        | some m =>
          simp only [ht] at h
          change some (subst filling sketch) = some result at h
          have h := Option.some.inj h
          subst result
          exact ⟨fu, m, rfl, rfl, infer_subst hu ht⟩
      · cases h

end Geb.Kernel

end
