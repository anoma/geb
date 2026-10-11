/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Compile
public import Geb.Prototypes.FreeTopos.Internal.Completeness
public import Geb.Prototypes.FreeTopos.Internal.Connectives
public import Geb.Prototypes.FreeTopos.Internal.Conversion
public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Development
public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.FreeTopos.Internal.Logic
public import Geb.Prototypes.FreeTopos.Internal.ObjectSubst
public import Geb.Prototypes.FreeTopos.Internal.Params
public import Geb.Prototypes.FreeTopos.Internal.Proofs
public import Geb.Prototypes.FreeTopos.Internal.Prove
public import Geb.Prototypes.FreeTopos.Internal.Represent
public import Geb.Prototypes.FreeTopos.Internal.Semantics
public import Geb.Prototypes.FreeTopos.Internal.Soundness
public import Geb.Prototypes.FreeTopos.Internal.Sorting
public import Geb.Prototypes.FreeTopos.Internal.Square
public import Geb.Prototypes.FreeTopos.Internal.Substitution
public import Geb.Prototypes.FreeTopos.Internal.Syntax
public import Geb.Prototypes.FreeTopos.Internal.SyntaxLaws

set_option doc.verso true in
/-!
# The internal language of the topos

The Mitchell–Bénabou language of the free elementary topos with data objects: its terms, with the
functor and monad laws of their renaming and substitution, their typing and compilation to the
combinators, its definitions, compiled to definitions of the
combinators, and the proof that compiling a term and unfolding the combinators' definitions
agrees, in every model, with unfolding the language's definitions and compiling; its derivations
of formulas under hypotheses, their checker and a prover, and the proofs that the checker is
sound and, citing certificates of the combinators, complete; its connectives, defined from
equality, with their rules derived, their meaning in every model, and description; and the
representation of Lean's functions by its terms in the topos of types and functional relations.
-/

set_option doc.verso true
