import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.Soundness.Collapse
import GebLean.Ramified.Characterization

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # The characterization

Part II chapter 5 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.2.
-/

#doc (Manual) "The characterization" =>

This chapter renders the seven endpoint declarations of `GebLean/Ramified/Soundness/Collapse.lean`
and `GebLean/Ramified/Characterization.lean`: the first-order syntactic category
{name GebLean.Ramified.SynCatFO}`SynCatFO`, and two triples — a soundness functor, its
faithfulness instance, and a definability theorem — that state the denotational form of
Leivant III's Theorem 14, items (1)-(2), section 6.1 {citep leivant3}[]. Both triples read the
same pair of results, once directly against the elementary-recursive Lawvere theory and once
transported across an equivalence to a further encoding. Part I chapter 6 states the complexity
connection this pair packages, with its own citations; the declarations below are that chapter's
promised formalization, and no proof is rendered here.

# The first-order syntactic category

{name GebLean.Ramified.SynCatFO}`SynCatFO` is the full subcategory of
{name GebLean.Ramified.RMRecCat}`RMRecCat natAlgSig` (Part II chapter 4) on the contexts all of
whose sorts are {tech}[object type]s — the boundary sorts Theorem 14 quantifies over, as against
the arbitrary r-types a ramified identifier's internal recurrence may still use. Both routes below
start from it and read a morphism's standard-model denotation through it, landing at
{name GebLean.LawvereERCat}`LawvereERCat`, the quotient Lawvere theory of elementary recursive
functions, once directly and once through a further encoding.

{docstring GebLean.Ramified.SynCatFO}

# The machine route

{name GebLean.Ramified.collapseFunctor}`collapseFunctor`, faithful by
{name GebLean.Ramified.collapseFunctor_faithful}`collapseFunctor_faithful`, and
{name GebLean.Ramified.ramified_definability}`ramified_definability` together state Theorem 14's
equivalence at the {name GebLean.Ramified.SynCatFO}`SynCatFO` /
{name GebLean.LawvereERCat}`LawvereERCat` level. The functor's object map reads off a context's
arity; its morphism map translates each morphism's components into Leivant III's applicative
calculus of section 4.1 and lands the translation as a class of
{name GebLean.LawvereERCat}`LawvereERCat`. Faithfulness states that this collapse identifies
nothing beyond what the two morphisms' own standard-model denotations already identify.
{name GebLean.Ramified.ramified_definability}`ramified_definability` closes the equivalence from
the other direction: every morphism of {name GebLean.LawvereERCat}`LawvereERCat` — every function
built from the zero, successor, projection, composition, bounded-sum, and bounded-product
generators — has an object-sort context and a {name GebLean.Ramified.SynCatFO}`SynCatFO` morphism
whose collapse denotation recovers it, up to the arity identification `objLen_toSynCatFO`. Its
witness is obtained by compiling the elementary-recursive morphism to a register-machine
computation and reading that computation's trace back as a ramified realizer, the route this
section takes its name from.

{docstring GebLean.Ramified.collapseFunctor}

{docstring GebLean.Ramified.collapseFunctor_faithful}

{docstring GebLean.Ramified.ramified_definability}

# The normalization route

{name GebLean.Ramified.collapseKFunctor}`collapseKFunctor`,
{name GebLean.Ramified.collapseKFunctor_faithful}`collapseKFunctor_faithful`, and
{name GebLean.Ramified.ramified_definability_kSim}`ramified_definability_kSim` restate the same
pair one encoding further on, in the depth-2 `K^sim` Lawvere theory
{name GebLean.LawvereKSimDCat}`LawvereKSimDCat 2` that {name GebLean.LawvereERCat}`LawvereERCat`
is categorically equivalent to ({name GebLean.erKSimEquiv}`erKSimEquiv`, Tourlakis's
Corollary 0.1.0.44 at `n = 2`). {name GebLean.Ramified.collapseKFunctor}`collapseKFunctor` is the
composite of {name GebLean.Ramified.collapseFunctor}`collapseFunctor` with the encoding
{name GebLean.erToKFunctor}`erToKFunctor`; its faithfulness follows from the faithfulness of each
factor. {name GebLean.Ramified.ramified_definability_kSim}`ramified_definability_kSim` restates
definability directly for `LawvereKSimDCat 2`: its witnesses are those of
{name GebLean.Ramified.ramified_definability}`ramified_definability` at the image of the given
morphism under the converse encoding {name GebLean.kToERFunctor}`kToERFunctor`, whose
interpretation the interp-preservation lemma
{name GebLean.kToERFunctor_map_interp}`kToERFunctor_map_interp` identifies with the original
morphism's.

{docstring GebLean.Ramified.collapseKFunctor}

{docstring GebLean.Ramified.collapseKFunctor_faithful}

{docstring GebLean.Ramified.ramified_definability_kSim}

This completes the manual's reference half. Part I chapter 6 identifies
{name GebLean.LawvereERCat}`LawvereERCat`'s functions with the Kalmár elementary functions and
cites Leivant III's Theorem 14 for that identification {citep leivant3}[]; the two triples above
are the repository's formalization of the theorem's (1)-(2) equivalence, relative to
{name GebLean.LawvereERCat}`LawvereERCat` rather than to an external machine model, and prove no
complexity bound beyond what the two categories' own definitions already fix.
