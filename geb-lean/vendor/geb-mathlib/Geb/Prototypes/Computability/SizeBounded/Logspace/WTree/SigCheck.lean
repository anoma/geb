/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigEdge

set_option doc.verso true in
/-!
# The algebra's expressions recognized by an expression of its own subalgebra

The recognizer of the W-trees of the algebra's own coded signature, with the
label and edge checks of that signature: an expression of the logspace
subalgebra that accepts exactly the spellings of the algebra's expressions,
{name}`Geb.SizeBounded.S`. In particular it accepts the spelling of every
expression of the subalgebra itself, its own included.

# Main definitions

* {lit}`sigRecognizer` — the recognizer.

# Main statements

* {lit}`sigRecognizer_iff` — the recognizer accepts a word exactly when the
  word spells an expression of the algebra.
* {lit}`sigRecognizer_spell` — the recognizer accepts the spelling of every
  expression, {lit}`sigRecognizer_self` the spelling of every expression of
  the subalgebra, and {lit}`sigRecognizer_sigRecognizer` its own.

# References

* \[Kristiansen2005\]
* \[Mazzanti2016\]

# Tags

logspace, size-bounded algebra, recognizer, self-recognition
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.SigCheck

open Sig SigLabel SigEdge
open Geb.SizeBounded (S)

public section

/-- The recognizer of the spellings of the algebra's expressions. -/
@[expose] def sigRecognizer : LOf 1 := recognizeExpr labelOk edgeOk

/-- The recognizer accepts a word exactly when it spells an expression of the
algebra. -/
theorem sigRecognizer_iff (y : List Bool) :
    sigRecognizer.sem ![y] = [true] ↔ ∃ e : S, sigCoded.spell e.1 = y := by
  rw [sigRecognizer, sigCoded.recognizeExprSem_eq_singleton_iff_isW labelOk edgeOk y
    (computesLabel y) (computesEdge y)]
  exact ⟨fun ⟨t, hv, hs⟩ ↦ ⟨⟨t, hv⟩, hs⟩, fun ⟨e, hs⟩ ↦ ⟨e.1, e.2, hs⟩⟩

/-- The recognizer accepts the spelling of every expression of the algebra. -/
theorem sigRecognizer_spell (e : S) : sigRecognizer.sem ![sigCoded.spell e.1] = [true] :=
  (sigRecognizer_iff _).mpr ⟨e, rfl⟩

/-- The recognizer accepts the spelling of every expression of the subalgebra,
its own included. -/
theorem sigRecognizer_self {n : ℕ} (e : LOf n) :
    sigRecognizer.sem ![sigCoded.spell e.1.1.1] = [true] :=
  sigRecognizer_spell e.1.1

/-- The recognizer accepts its own spelling. -/
theorem sigRecognizer_sigRecognizer :
    sigRecognizer.sem ![sigCoded.spell sigRecognizer.1.1.1] = [true] :=
  sigRecognizer_self sigRecognizer

end

end Geb.SizeBounded.Logspace.WTree.SigCheck
