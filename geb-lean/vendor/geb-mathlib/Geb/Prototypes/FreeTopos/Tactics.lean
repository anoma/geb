/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Tactics.Reduction

set_option doc.verso true in
/-!
# Tactics of the internal language

Provers of the internal language's equations composed from the prover
({name}`Geb.FreeTopos.Internal.byNorm` and the provers beside it): proofs by reduction, by
induction and case analysis, with hypotheses, by search, and about the translation's trees. The
proofs about the compiler's components made in the language compose them.
-/

set_option doc.verso true
