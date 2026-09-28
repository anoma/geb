/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover.Induction
public import Geb.Prototypes.FreeTopos.Prover.Library
public import Geb.Prototypes.FreeTopos.Prover.Rewrite
public import Geb.Prototypes.FreeTopos.Prover.Tactic
public import Geb.Prototypes.FreeTopos.Prover.Typing

set_option doc.verso true in
/-!
# A prover for the theory of an elementary topos

The metalogic's prover, prototyped in Lean: it computes certificates that the checker
{name}`Geb.PartialHorn.check` checks, by typing terms, rewriting them with the axioms and the
equations of a development, and the tactics a proof is written in. The prover is not trusted:
a development it produces is valid in every model when it checks.
-/

set_option doc.verso true
