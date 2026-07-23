import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.Term
import GebLean.Ramified.Interp
import GebLean.Ramified.SynCat
import GebLean.Ramified.RType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # The Lawvere-theory layer

Part II chapter 3 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.2.
-/

#doc (Manual) "The Lawvere-theory layer" =>

This chapter renders the declarations of `GebLean/Ramified/Term.lean`,
`GebLean/Ramified/Interp.lean`, and `GebLean/Ramified/SynCat.lean`: the term
algebra of a multi-sorted signature, its evaluation in a model, and the
category those terms form. Together the three modules present a free
multi-sorted Lawvere theory — the clone of a signature's terms, quotiented by
a congruence — as the syntactic category underlying the higher-order system
of Part II chapter 4.

# The term algebra and its clone laws

A context is a list of sorts; {name GebLean.Ramified.SortedSig.polyEndo}`SortedSig.polyEndo`
reads a {name GebLean.Ramified.SortedSig}`SortedSig` (Part II chapter 2) as an
indexed polynomial endofunctor on the sort type, and {name GebLean.Ramified.Tm}`Tm` is the
free monad of that endofunctor at a context's variable family.
{name GebLean.Ramified.Tm.var}`Tm.var` and {name GebLean.Ramified.Tm.op}`Tm.op` are the free
monad's unit and node constructors; {name GebLean.Ramified.Tm.subst}`Tm.subst` is its bind,
and {name GebLean.Ramified.Tm.subst_id}`Tm.subst_id`,
{name GebLean.Ramified.Tm.subst_subst}`Tm.subst_subst`,
{name GebLean.Ramified.Tm.var_subst}`Tm.var_subst` are, respectively, the free monad's
right-unit, associativity, and left-unit laws, read as the clone laws of the term algebra.
{name GebLean.Ramified.Tm.weaken}`Tm.weaken` is the special case of
{name GebLean.Ramified.Tm.subst}`Tm.subst` that substitutes variables for variables along a
sort-preserving renaming. {name GebLean.Ramified.QuotRel}`QuotRel` closes the section: it
packages a per-context, per-sort setoid on terms with the fact that substitution respects it
in both positions, the data a quotient of the term algebra needs to compose. The two
instantiations this chapter and the next put to use are
{name GebLean.Ramified.interpQuotRel}`interpQuotRel`, below, and a derivability relation
supplied by the deferred equational workstream.

{docstring GebLean.Ramified.Ctx}

{docstring GebLean.Ramified.SortedSig.polyEndo}

{docstring GebLean.Ramified.Tm}

{docstring GebLean.Ramified.Tm.var}

{docstring GebLean.Ramified.Tm.op}

{docstring GebLean.Ramified.Tm.subst}

{docstring GebLean.Ramified.Tm.subst_id}

{docstring GebLean.Ramified.Tm.subst_subst}

{docstring GebLean.Ramified.Tm.var_subst}

{docstring GebLean.Ramified.Tm.weaken}

{docstring GebLean.Ramified.QuotRel}

# Models, the standard interpretation, and the interpretative quotient

A {name GebLean.Ramified.SortedModel}`SortedModel` interprets a signature set-theoretically:
a carrier per sort and, for each operation, a function from argument values to a result
value. {name GebLean.Ramified.SortedModel.Env}`SortedModel.Env` is an environment over a
context — a carrier element at each position, of that position's sort — and
{name GebLean.Ramified.Tm.eval}`Tm.eval` folds a term against a model over an environment,
following the free monad's own fold.
{name GebLean.Ramified.Tm.eval_subst}`Tm.eval_subst` is the semantic counterpart of the clone
laws above: evaluating a substituted term equals evaluating the term under the environment
obtained by evaluating the substitution. A {name GebLean.Ramified.Presentation}`Presentation`
bundles a sort type, a signature, an object-sort predicate carried as data — the predicate
that, instantiated at {name GebLean.Ramified.RType}`RType` (Part II chapter 2), recovers the
{tech}[object type]s — a base free-algebra signature, and a standard model;
{name GebLean.Ramified.standardModel}`standardModel` is the designated-model projection.
{name GebLean.Ramified.interpSetoid}`interpSetoid` relates two terms of a presentation when
they evaluate equally at the standard model under every environment, and
{name GebLean.Ramified.interpQuotRel}`interpQuotRel` packages the
{name GebLean.Ramified.interpSetoid}`interpSetoid` family with its substitution-congruence
law as a {name GebLean.Ramified.QuotRel}`QuotRel`, discharged by
{name GebLean.Ramified.Tm.eval_subst}`Tm.eval_subst`. This is the quotient relation the
syntactic category below instantiates.

{docstring GebLean.Ramified.SortedModel}

{docstring GebLean.Ramified.SortedModel.Env}

{docstring GebLean.Ramified.Tm.eval}

{docstring GebLean.Ramified.Tm.eval_subst}

{docstring GebLean.Ramified.Presentation}

{docstring GebLean.Ramified.standardModel}

{docstring GebLean.Ramified.interpSetoid}

{docstring GebLean.Ramified.interpQuotRel}

# The syntactic category and its finite products

{name GebLean.Ramified.HomTuple}`HomTuple` is the raw morphism data of the syntactic
category: a codomain-indexed tuple of domain terms.
{name GebLean.Ramified.Hom}`Hom` quotients {name GebLean.Ramified.HomTuple}`HomTuple` by the
pointwise closure of a {name GebLean.Ramified.QuotRel}`QuotRel`, and
{name GebLean.Ramified.SynCat}`SynCat` is the resulting category's carrier, a type synonym
for {name GebLean.Ramified.Ctx}`Ctx` carrying the relation as a phantom parameter so that
distinct relations give distinct instances on the same carrier.
{name GebLean.Ramified.SynCat.instCategory}`SynCat.instCategory` takes the identity morphism
to the variable tuple and composition to substitution, so that the category laws are exactly
the clone laws of the section above, transported to the quotient.
{name GebLean.Ramified.SynCat.instCartesianMonoidalCategory}`SynCat.instCartesianMonoidalCategory`
exhibits chosen finite products by context concatenation, making the syntactic category a
{name CategoryTheory.CartesianMonoidalCategory}`CartesianMonoidalCategory`.
{name GebLean.Ramified.HomTuple.eval}`HomTuple.eval` evaluates a morphism tuple componentwise
at an environment of a model; {name GebLean.Ramified.Hom.eval}`Hom.eval` is its lift along
{name GebLean.Ramified.interpQuotRel}`interpQuotRel` to the standard model, well-defined
because that relation identifies exactly the tuples with equal evaluations.
{name GebLean.Ramified.Hom.eval_mk}`Hom.eval_mk` computes the lift at a representative.
{name GebLean.Ramified.HomTuple.eval_comp}`HomTuple.eval_comp` and
{name GebLean.Ramified.Hom.eval_comp}`Hom.eval_comp` state that evaluation respects
composition, at the tuple level and at the quotient level respectively — each an instance of
{name GebLean.Ramified.Tm.eval_subst}`Tm.eval_subst` applied componentwise.

{docstring GebLean.Ramified.HomTuple}

{docstring GebLean.Ramified.Hom}

{docstring GebLean.Ramified.SynCat}

{docstring GebLean.Ramified.SynCat.instCategory}

{docstring GebLean.Ramified.SynCat.instCartesianMonoidalCategory}

{docstring GebLean.Ramified.HomTuple.eval}

{docstring GebLean.Ramified.Hom.eval}

{docstring GebLean.Ramified.Hom.eval_mk}

{docstring GebLean.Ramified.HomTuple.eval_comp}

{docstring GebLean.Ramified.Hom.eval_comp}
