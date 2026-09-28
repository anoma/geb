/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Arrows
public import Geb.Prototypes.FreeTopos.Category
public import Geb.Prototypes.FreeTopos.Check
public import Geb.Prototypes.FreeTopos.Chosen
public import Geb.Prototypes.FreeTopos.Classifier
public import Geb.Prototypes.FreeTopos.Coequalizers
public import Geb.Prototypes.FreeTopos.Converse
public import Geb.Prototypes.FreeTopos.Coproducts
public import Geb.Prototypes.FreeTopos.Elementary
public import Geb.Prototypes.FreeTopos.Graphs
public import Geb.Prototypes.FreeTopos.Infer
public import Geb.Prototypes.FreeTopos.Internal
public import Geb.Prototypes.FreeTopos.Model
public import Geb.Prototypes.FreeTopos.Prover
public import Geb.Prototypes.FreeTopos.Recursion
public import Geb.Prototypes.FreeTopos.Relations
public import Geb.Prototypes.FreeTopos.Represent
public import Geb.Prototypes.FreeTopos.Theory
public import Geb.Prototypes.FreeTopos.Topos
public import Geb.Prototypes.FreeTopos.Unfolding
public import Geb.Prototypes.FreeTopos.UniqueChoice
public import Geb.Prototypes.FreeTopos.UniqueChoiceClassical

set_option doc.verso true in
/-!
# The free elementary topos with data objects

The metalogic's presentation of the free elementary topos with the natural numbers, list and
rose-tree objects, as a partial Horn theory whose sorts are objects and arrows, with the proof
that the category of each of its models is an elementary topos, a checker that infers the
typing of the terms of its certificates, a prover that computes certificates in it, the
uniqueness of its folds with a parameter, the distributivity of its products over its coproducts,
its internal language, compiled to its combinators, toposes with chosen structure in dependent
form, each a model of the theory, among them each elementary topos of the repository's class
with chosen data objects, and the topos of Lean's types and functional relations, in
which Lean's functions are the graphs, so that the theory's theorems about arrows are Lean's
about functions, and in which an arrow, its definitions unfolded, represents a Lean function
between representations of its values; and the translation of the kernel's programs into the
internal language.
-/

set_option doc.verso true
