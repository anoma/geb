import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.HigherOrder
import GebLean.Ramified.OmegaShift
import GebLean.Ramified.Examples

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # The higher-order system and its instantiations

Part II chapter 4 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.2.
-/

#doc (Manual) "The higher-order system and its instantiations" =>

This chapter renders the declarations of `GebLean/Ramified/HigherOrder.lean` and
`GebLean/Ramified/OmegaShift.lean`: the higher-order system of Leivant III section 2.3 — the
application operations, the schema-generated identifiers, and the multi-sorted presentation and
syntactic category they assemble — together with the auxiliary coercions of section 2.4(1) at
every {tech}[r-type]. Part I chapters 4 and 5 read the same material as a typing discipline and
as a worked ladder of examples; the prose here places each declaration in relation to its
neighbours. The system's instantiation over the monadic word algebra follows in a later section
of this chapter.

# Application and constructor interpretation over the standard carriers

The higher-order system adds one further signature to the constructor summand of Part II
chapter 2: for every pair of r-types `(σ, τ)`, {name GebLean.Ramified.appSig}`appSig` supplies an
operation of arity `[σ → τ, σ]` and result `τ`, applying a function to an argument. Two
functions read operations over the standard carriers `RType.interp (FreeAlg A)`:
{name GebLean.Ramified.stdConstructorInterp}`stdConstructorInterp` reads a
{name GebLean.Ramified.constructorSig}`constructorSig` operation (Part II chapter 2) as the
free-algebra node {name GebLean.Ramified.FreeAlg.mk}`FreeAlg.mk`, and
{name GebLean.Ramified.stdAppInterp}`stdAppInterp` reads an
{name GebLean.Ramified.appSig}`appSig` operation as function
application, taking the first argument as a function at `σ → τ` and applying it to the second.

{docstring GebLean.Ramified.appSig}

{docstring GebLean.Ramified.stdConstructorInterp}

{docstring GebLean.Ramified.stdAppInterp}

# Currying and the application chain

An identifier's context `Γ` and result sort `τ` also present it, as a value, at a curried arrow
sort. {name GebLean.Ramified.RType.curried}`RType.curried` computes that sort,
`Γ.foldr RType.arrow τ`, the r-type `σ₁ → ⋯ → σₙ → τ` for `Γ = [σ₁, …, σₙ]`.
{name GebLean.Ramified.curryInterp}`curryInterp` builds a value at the curried sort from a
function on environments over `Γ`, consuming the context one sort at a time;
{name GebLean.Ramified.appChain}`appChain` is the corresponding operation reading a value at a
curried sort back down against an argument environment, one position at a time.
{name GebLean.Ramified.appChain_curryInterp}`appChain_curryInterp` proves the two mutually
invert: applying {name GebLean.Ramified.appChain}`appChain` to a value built by
{name GebLean.Ramified.curryInterp}`curryInterp` from `g` and an environment `ρ`
recovers `g ρ`. {name GebLean.Ramified.appChain_stdConstructorInterp}`appChain_stdConstructorInterp`
specializes this at a constructor operation, the semantic constructor node rule: the application
chain of a curried constructor interpretation, applied to a full argument spine and read at the
object sort, is the free-algebra node {name GebLean.Ramified.FreeAlg.mk}`FreeAlg.mk` on the
arguments.

{docstring GebLean.Ramified.RType.curried}

{docstring GebLean.Ramified.curryInterp}

{docstring GebLean.Ramified.appChain}

{docstring GebLean.Ramified.appChain_curryInterp}

{docstring GebLean.Ramified.appChain_stdConstructorInterp}

# Hole signatures and explicit definitions

An explicit definition's defining term is built over the constructor and application operations
together with one further pair of summands per identifier occurrence.
{name GebLean.Ramified.holeSig}`holeSig` reads an occurrence as a saturated application, taking
arguments at the referenced identifier's context and returning a value at its result sort;
{name GebLean.Ramified.holeConstSig}`holeConstSig` reads the same occurrence as a nullary
combinator value at the identifier's curried arrow sort, to be applied through
{name GebLean.Ramified.appSig}`appSig`. {name GebLean.Ramified.defnSig}`defnSig` assembles the
base signature of a definition's body from the four summands: the object-sort constructors,
application, the saturated holes, and their curried-combinator forms.
{name GebLean.Ramified.DefnShape}`DefnShape` packages an explicit definition's non-recursive
data — the number of holes, each hole's context and result sort, and the defining term over
{name GebLean.Ramified.defnSig}`defnSig` at those holes.

{docstring GebLean.Ramified.holeSig}

{docstring GebLean.Ramified.holeConstSig}

{docstring GebLean.Ramified.defnSig}

{docstring GebLean.Ramified.DefnShape}

# The recurrence schema shapes

{name GebLean.Ramified.MrecShape}`MrecShape` and {name GebLean.Ramified.FrecShape}`FrecShape`
package the non-recursive data of the two recurrence schema formers: parameters at r-types the
caller chooses, together with a proof that the context is the parameters followed by the
recurrence argument's sort — `RType.omega τ` for a {tech}[monotonic] recurrence (Leivant III
eq. (4)), {name GebLean.Ramified.RType.o}`RType.o` for a {tech}[flat] recurrence (eq. (5)).
{name GebLean.Ramified.IdentShape}`IdentShape` is the disjoint union of the three formers'
shapes — {name GebLean.Ramified.DefnShape}`DefnShape`, {name GebLean.Ramified.MrecShape}`MrecShape`,
{name GebLean.Ramified.FrecShape}`FrecShape` — at a context and result sort;
{name GebLean.Ramified.identEndo}`identEndo` reads it, together with the direction type mapping a
shape to the identifiers it refers to, as the indexed signature endofunctor over
`List RType × RType` (context, result sort) whose fixed point is the identifier type below.

{docstring GebLean.Ramified.MrecShape}

{docstring GebLean.Ramified.FrecShape}

{docstring GebLean.Ramified.IdentShape}

{docstring GebLean.Ramified.identEndo}

# The schema-generated identifiers

{name GebLean.Ramified.RIdent}`RIdent A Γ τ` is the fixed point of
{name GebLean.Ramified.identEndo}`identEndo` at the index `(Γ, τ)`: the schema-generated
identifiers over the base algebra `A`, indexed by their context and result sort.
{name GebLean.Ramified.RIdent.defn}`RIdent.defn`, {name GebLean.Ramified.RIdent.mrec}`RIdent.mrec`,
and {name GebLean.Ramified.RIdent.frec}`RIdent.frec` are the three derived formers, each
packaging a shape's non-recursive data together with the identifiers filling its children.
{name GebLean.Ramified.RIdent.mrec}`RIdent.mrec` types the recurrence argument at
`RType.omega τ` and the {tech}[recursive results] and output at `τ`: the recurrence argument
sits one {tech}[tier] above the output. {name GebLean.Ramified.RIdent.frec}`RIdent.frec`
instead types the recurrence argument directly at
{name GebLean.Ramified.RType.o}`RType.o`, with no tier spent, since a
{tech}[flat] recurrence produces no recursive result to license.
{name GebLean.Ramified.RIdent.interp}`RIdent.interp` denotes an identifier as a function from an
environment over its context to a value at its result sort, over the standard carriers.
{name GebLean.Ramified.RIdent.interp_defn}`RIdent.interp_defn` and
{name GebLean.Ramified.RIdent.mrec_interp}`RIdent.mrec_interp` are two of its definitional
reduction rules: the former unfolds an explicit-definition node to evaluating its body against
the model whose hole readings are the children's denotations; the latter unfolds a
monotonic-recurrence node at the empty parameter context to the free-algebra recurrence
{name GebLean.Ramified.FreeAlg.recurse}`FreeAlg.recurse` over its step functions, run on the
recurrence argument.

{docstring GebLean.Ramified.RIdent}

{docstring GebLean.Ramified.RIdent.defn}

{docstring GebLean.Ramified.RIdent.mrec}

{docstring GebLean.Ramified.RIdent.frec}

{docstring GebLean.Ramified.RIdent.interp}

{docstring GebLean.Ramified.RIdent.interp_defn}

{docstring GebLean.Ramified.RIdent.mrec_interp}

# The two identifier surfacings

Every identifier admits two readings as an operation of a multi-sorted signature.
{name GebLean.Ramified.identSig}`identSig` reads it as a saturated operation, of its context as
arity and result sort as result; {name GebLean.Ramified.identConstSig}`identConstSig` reads it as
a nullary combinator constant at its curried arrow sort, dual to
{name GebLean.Ramified.holeConstSig}`holeConstSig`'s reading of an occurrence within a
definition's body.
{name GebLean.Ramified.RIdent.interp_eq_appChain_curryInterp}`RIdent.interp_eq_appChain_curryInterp`
states their coherence: the saturated identifier's denotation equals the application chain of its
constant's denotation, so the two readings agree extensionally wherever both are defined.

{docstring GebLean.Ramified.identSig}

{docstring GebLean.Ramified.identConstSig}

{docstring GebLean.Ramified.RIdent.interp_eq_appChain_curryInterp}

# The higher-order presentation and its syntactic category

{name GebLean.Ramified.higherOrder}`higherOrder` assembles the full presentation over a base
algebra `A`: the object-sort constructors, application, the saturated identifiers, and their
curried constants, summed by {name GebLean.Ramified.SortedSig.sum}`SortedSig.sum` (Part II
chapter 2), with the standard model interpreting every operation over the standard carriers via
the interpretation functions above. {name GebLean.Ramified.RMRecCat}`RMRecCat` is the resulting
syntactic category — the generic construction {name GebLean.Ramified.SynCat}`SynCat` (Part II
chapter 3) instantiated at `higherOrder A` under interpretative equality at the standard model.
{name GebLean.Ramified.identHom}`identHom` lifts an identifier `f : RIdent A Γ τ` to the morphism
`Γ ⟶ [τ]` of `RMRecCat A` applying `f`'s saturated operation to the context's variables;
{name GebLean.Ramified.identHom_eval}`identHom_eval` states that its standard-model evaluation
reads off {name GebLean.Ramified.RIdent.interp}`RIdent.interp` directly.

{docstring GebLean.Ramified.higherOrder}

{docstring GebLean.Ramified.RMRecCat}

{docstring GebLean.Ramified.identHom}

{docstring GebLean.Ramified.identHom_eval}

# The Omega shift on sorts

{name GebLean.Ramified.RType.omegaShift}`RType.omegaShift` is the base substitution
`τ[o := Ω o]` on r-types: it sends the base sort `o` to `RType.omega RType.o` and commutes with
{name GebLean.Ramified.RType.arrow}`RType.arrow` and
{name GebLean.Ramified.RType.omega}`RType.omega`, changing only the occurrences of `o` and not
the r-type's arrow structure. It is a sort-level construction only; no endofunctor of
{name GebLean.Ramified.RMRecCat}`RMRecCat` over the shift is built here.

{docstring GebLean.Ramified.RType.omegaShift}

# Kappa-hat at object sorts

Leivant III section 2.4(1) supplies an auxiliary coercion kappa-hat, `kappa-hat_τ : Ω τ → τ`, at
every r-type `τ`, defined by ramified recurrence through the pointwise constructor lifts of that
section. {name GebLean.Ramified.kappaHatIdent}`kappaHatIdent` is its instance at an
{tech}[object type] `τ`: a {tech}[monotonic] recurrence whose recurrence argument sits at
`RType.omega τ` and whose step function at each constructor applies that constructor at `τ` to
the {tech}[recursive results], reconstructing the argument. Because every {tech}[object type]
denotes a copy of the algebra's carrier,
{name GebLean.Ramified.kappaHatIdent_interp}`kappaHatIdent_interp` states that its denotation is
the identity on that carrier.
{name GebLean.Ramified.kappaHat}`kappaHat` restates
{name GebLean.Ramified.kappaHatIdent}`kappaHatIdent` as a morphism `[Ω τ] ⟶ [τ]` of `RMRecCat A`
at the singleton contexts, and {name GebLean.Ramified.kappaHat_interp}`kappaHat_interp` transports
the identity reading to the underlying morphism tuple's standard-model evaluation.

{docstring GebLean.Ramified.kappaHatIdent}

{docstring GebLean.Ramified.kappaHatIdent_interp}

{docstring GebLean.Ramified.kappaHat}

{docstring GebLean.Ramified.kappaHat_interp}

# The curried decomposition of an r-type

Every r-type factors as `τ = σ-vec → θ`, a curried arrow over an {tech}[object type] `θ`.
{name GebLean.Ramified.RType.objTarget}`RType.objTarget` computes the target `θ`: an
{tech}[object type] is its own target, and an arrow's target is its codomain's target.
{name GebLean.Ramified.RType.domains}`RType.domains` computes the domain list `σ-vec`, empty at
an {tech}[object type] and extended by one domain per arrow layer otherwise. Together the two
witness `τ = RType.curried τ.domains τ.objTarget`, the decomposition the constructions below
recurse on.

{docstring GebLean.Ramified.RType.objTarget}

{docstring GebLean.Ramified.RType.domains}

# The pointwise constructor lift and kappa-hat at every r-type

The paper's kappa-hat is defined at every r-type, not only at {tech}[object type]s, by ramified
recurrence through the pointwise constructor lift `c_i^τ`. At an object type the lift is the
constructor operation itself; at an arrow sort `σ → ρ`,
{name GebLean.Ramified.cLiftArrow}`cLiftArrow` builds the lift over `σ → ρ` from a lift over the
codomain `ρ`, following `c_i^{σ → ρ}(u-vec)(x) = c_i^ρ(u₁ x, …, u_r x)` — an explicit definition
applying the codomain lift to the pointwise applications of each argument to `x`.
{name GebLean.Ramified.cLiftArrow_interp}`cLiftArrow_interp` states that its denotation matches
that equation directly. {name GebLean.Ramified.cLift}`cLift` assembles the pointwise lift at an
arbitrary r-type: the constructor operation at an object type, and
{name GebLean.Ramified.cLiftArrow}`cLiftArrow` iterated over the curried decomposition
otherwise. {name GebLean.Ramified.kappaHatFull}`kappaHatFull` is the resulting kappa-hat at every
r-type, the {tech}[monotonic] recurrence with steps {name GebLean.Ramified.cLift}`cLift`;
{name GebLean.Ramified.kappaHatFull_interp}`kappaHatFull_interp` states that its denotation
unfolds, by definition, to the free-algebra recurrence over those steps run on the recurrence
argument. {name GebLean.Ramified.kappaHatFull_eq_kappaHatIdent}`kappaHatFull_eq_kappaHatIdent`
states that the two constructions agree at object types, where the pointwise lift specializes to
the constructor operation {name GebLean.Ramified.kappaHatIdent}`kappaHatIdent` already uses.

{docstring GebLean.Ramified.cLiftArrow}

{docstring GebLean.Ramified.cLiftArrow_interp}

{docstring GebLean.Ramified.cLift}

{docstring GebLean.Ramified.kappaHatFull}

{docstring GebLean.Ramified.kappaHatFull_interp}

# The canonical functionals and the downward coercions

Leivant III section 2.4(1)'s coercion `kappa_τ : Ω τ → θ` (with `θ = τ.objTarget`) lowers the
arrow structure of `τ` by feeding kappa-hat's output the canonical functionals of `τ`'s domains.
{name GebLean.Ramified.canonIdent}`canonIdent` is the canonical functional `C^τ = λ x-vec. α^θ`
at a domain sort: the constant functional returning the object algebra's designated 0-ary
constructor `α^θ`, carried as a label `b₀` together with a nullary-arity witness `h₀`.
{name GebLean.Ramified.applyCanon}`applyCanon` is the saturating half of the coercion: an
explicit definition applying a `τ`-valued input to the canonical functionals of each of `τ`'s
domains in turn; {name GebLean.Ramified.applyCanon_interp}`applyCanon_interp` states that its
denotation is the application chain of the (curried-decomposition-transported) input over those
canonical functionals. {name GebLean.Ramified.kappaIdent}`kappaIdent` composes the two —
{name GebLean.Ramified.kappaHatFull}`kappaHatFull` postcomposed with
{name GebLean.Ramified.applyCanon}`applyCanon` — so that
`kappa_τ(u) = (kappa-hat_τ u)(C^{σ₁}, …, C^{σ_k})`.
{name GebLean.Ramified.kappaIdent_interp}`kappaIdent_interp` states that, like kappa-hat itself,
it denotes the identity on the carrier copy. {name GebLean.Ramified.deltaIdent}`deltaIdent` is
the companion downward coercion `delta_θ : θ → o` at an {tech}[object type] `θ`: the composite of
{name GebLean.Ramified.kappaIdent}`kappaIdent` applied down through `θ`'s structure until the
base sort `o` is reached, generalizing the tower-sorted downward coercion of Part I chapter 5 to
an arbitrary object type. {name GebLean.Ramified.deltaIdent_interp}`deltaIdent_interp` states
that it, too, denotes the identity on the carrier copy.

{docstring GebLean.Ramified.canonIdent}

{docstring GebLean.Ramified.applyCanon}

{docstring GebLean.Ramified.applyCanon_interp}

{docstring GebLean.Ramified.kappaIdent}

{docstring GebLean.Ramified.kappaIdent_interp}

{docstring GebLean.Ramified.deltaIdent}

{docstring GebLean.Ramified.deltaIdent_interp}

# Successor, addition, and multiplication

The remainder of this chapter renders `GebLean/Ramified/Examples.lean`: Leivant III section
2.4's ladder of examples over the monadic word algebra
{name GebLean.Ramified.natAlgSig}`natAlgSig`, the `1 + X` algebra of the unary naturals
{citep leivant3}[]. Each example is a schema identifier of the higher-order system above,
interpreted on the standard carrier `FreeAlg natAlgSig` by an interpretation lemma stated
through the numeric reading {name GebLean.Ramified.natToFreeAlg}`natToFreeAlg` and
{name GebLean.Ramified.freeAlgToNat}`freeAlgToNat` (`GebLean/Ramified/AlgSig.lean`). Part I
chapter 5 reads the same ladder as a worked sequence of examples; the prose here places each
identifier and its interpretation lemma in relation to its neighbours.

{name GebLean.Ramified.ramSucc}`ramSucc`, at context `[RType.o]` and result `RType.o`, is the
successor-wrapper identifier `sc (x) = succ x`: an explicit definition applying the object
algebra's unary constructor to its argument. It carries no recurrence of its own; the
exponentiation clauses below apply its curried combinator form as the function iterated by the
second-order recurrence for `e`.

Leivant III section 2.4(2) defines addition and multiplication over
{name GebLean.Ramified.natAlgSig}`natAlgSig`'s single unary constructor, each a
{tech}[monotonic] recurrence. {name GebLean.Ramified.ramAdd}`ramAdd`, at context
`[RType.o, RType.omega RType.o]` and result `RType.o`, recurs on the second argument with the
first as {tech}[recurrence parameters]: `a + 0 = a` and `a + (n + 1) = (a + n) + 1`.
{name GebLean.Ramified.ramMul}`ramMul`, at context `[RType.omega RType.o, RType.omega RType.o]`
and result `RType.o`, recurs on the second argument with the first — itself at
`RType.omega RType.o` — as parameter: `x * 0 = 0` and `x * (n + 1) = x * n + x`, the inner
addition supplied by {name GebLean.Ramified.ramAdd}`ramAdd` through a hole.

{name GebLean.Ramified.ramAdd_interp}`ramAdd_interp` states that on natural-number inputs `a`
and `b` the denotation of {name GebLean.Ramified.ramAdd}`ramAdd` reads out, by
{name GebLean.Ramified.freeAlgToNat}`freeAlgToNat`, as `a + b`.
{name GebLean.Ramified.ramMul_interp}`ramMul_interp` states the corresponding fact for
{name GebLean.Ramified.ramMul}`ramMul`: on inputs `x` and `y` the denotation reads out as
`x * y`.

{docstring GebLean.Ramified.ramSucc}

{docstring GebLean.Ramified.ramAdd}

{docstring GebLean.Ramified.ramAdd_interp}

{docstring GebLean.Ramified.ramMul}

{docstring GebLean.Ramified.ramMul_interp}

# The size function

Leivant III section 2.4(6) defines a size function `sz` by a {tech}[monotonic] recurrence with
no {tech}[recurrence parameters]: its recurrence argument sits at `RType.omega RType.o` and its
{tech}[recursive results] at `RType.o`. {name GebLean.Ramified.ramSize}`ramSize`, at context
`[RType.omega RType.o]` and result `RType.o`, is that recurrence: `sz (0) = 0` and
`sz (n + 1) = sz (n) + 1`. Over the `1 + X` word algebra a recursive result rebuilds the count
of its subterm at each step, so the recurrence is extensionally the identity; the paper's exact
typing for `sz` was not independently verified, and the shape rendered here follows the
schema's general monotonic form.

{name GebLean.Ramified.ramSize_interp}`ramSize_interp` states this identity: for a carrier
element `t`, the denotation of {name GebLean.Ramified.ramSize}`ramSize` on the environment
carrying `t` reads out, by {name GebLean.Ramified.freeAlgToNat}`freeAlgToNat`, as the count of
`t` itself.

{docstring GebLean.Ramified.ramSize}

{docstring GebLean.Ramified.ramSize_interp}

# Composition, exponentiation, and the two-power ladder

{name GebLean.Ramified.ramFun}`ramFun` names the r-type `RType.arrow RType.o RType.o`, the
function sort at which the identifiers below take their values; it is rendered here so that
their types below carry no unrendered name.

{name GebLean.Ramified.ramComp}`ramComp`, at context `[ramFun, ramFun, RType.o]` and result
`RType.o`, is the two-fold-application identifier `comp (f, g, x) = f (g x)`: an explicit
definition applying its two function arguments to its third argument in turn through the
application former. Its curried combinator form is what the exponentiation step clause below
uses to compose a recursive result with itself.

Leivant III section 2.4(3) defines an exponentiation `e` by second-order recurrence, the
ladder's turn: it recurs at the function sort {name GebLean.Ramified.ramFun}`ramFun` rather
than at an {tech}[object type], so its {tech}[recursive results] are themselves functions and
its recurrence argument sits at `RType.omega ramFun`, one {tech}[tier] above the output.
{name GebLean.Ramified.ramExp}`ramExp`, at context `[RType.omega ramFun]` and result
{name GebLean.Ramified.ramFun}`ramFun`, is the recurrence `e (0) = sc` and
`e (n + 1) = e (n) ∘ e (n)`, where `sc` is
{name GebLean.Ramified.ramSucc}`ramSucc`'s combinator form and `∘` is
{name GebLean.Ramified.ramComp}`ramComp`'s; self-composing the recursive result at every step,
rather than applying the step function once more to it, is what turns `2^n`-fold repetition of
the successor into `2^{n+1}`-fold repetition.

{name GebLean.Ramified.ramExp_interp}`ramExp_interp` states the resulting semantics: for a
recurrence argument `ρ 0` at `RType.omega ramFun` and an input `x`, the denotation
`(ramExp.interp ρ) x` has count `freeAlgToNat x + 2 ^ freeAlgToNat (ρ 0)`.

Leivant III section 2.4(4) iterates `e` to build the ladder `2_m`: `2_0 (x) = x` and
`2_{m+1} (x) = 2 ^ (2_m (x))`. No identifier realizes this iteration directly — the tier
discipline forbids a raising coercion into a strictly higher tier, so the `m`-fold composite of
`e` cannot be assembled as a single schema identifier whose recurrence argument is itself the
output of a previous stage. {name GebLean.Ramified.ramTwoPow}`ramTwoPow` instead composes, at
the carrier level, `m` applications of the single exponential step obtained by driving
{name GebLean.Ramified.ramExp}`ramExp` with its argument and evaluating the result at `0`.

{name GebLean.Ramified.ramTwoPow_interp}`ramTwoPow_interp` states that on a carrier element
`x`, the count of `ramTwoPow m x` equals `GebLean.tower m (freeAlgToNat x)`, the height-`m`
tower of twos ({name GebLean.tower}`GebLean.tower`, `GebLean/Utilities/Tower.lean`) applied to
the count of `x`.

{docstring GebLean.Ramified.ramFun}

{docstring GebLean.Ramified.ramComp}

{docstring GebLean.Ramified.ramExp}

{docstring GebLean.Ramified.ramExp_interp}

{docstring GebLean.Ramified.ramTwoPow}

{docstring GebLean.Ramified.ramTwoPow_interp}

# The kappa and delta coercions

Leivant III section 2.4(1) supplies two downward coercions between {tech}[object type]s, both
extensionally the identity on the carrier; this development instantiates them over the
tower-sort chain of {tech}[tier]s that chapter 3 built.
{name GebLean.Ramified.objToNat}`objToNat` is the numeric reading of an object-sort carrier
value through the carrier-copy equality a tower sort carries, needed because a tower sort's
denotation does not reduce syntactically to the carrier for a symbolic tier index.

{name GebLean.Ramified.ramKappa}`ramKappa` is the single `Omega`-lowering step, from
`RType.tower (m + 1)` to `RType.tower m` for a natural number `m`:
{name GebLean.Ramified.kappaHatIdent}`kappaHatIdent` (`GebLean/Ramified/OmegaShift.lean`)
instantiated at the object type `RType.tower m`, an identifier whose recurrence reconstructs
its argument constructor by constructor. {name GebLean.Ramified.ramDeltaIdent}`ramDeltaIdent`
composes {name GebLean.Ramified.ramKappa}`ramKappa` at every step from `RType.tower m` down to
`RType.o`, an `m`-fold composite lowering a tower sort all the way to the base object sort.

{name GebLean.Ramified.ramKappa_interp}`ramKappa_interp` reads the denotation of `ramKappa m`
on an environment `ρ` at context `[RType.tower (m + 1)]` — at the lower tower sort
`RType.tower m` — as the numeric reading of `ρ 0` at the higher tower sort
`RType.tower (m + 1)`. {name GebLean.Ramified.ramDeltaIdent_interp}`ramDeltaIdent_interp` reads
the denotation of `ramDeltaIdent m` on an environment `ρ` at context `[RType.tower m]`,
directly by {name GebLean.Ramified.freeAlgToNat}`freeAlgToNat` since its result sort is
`RType.o`, as the numeric reading of `ρ 0` at that same tower sort `RType.tower m`. Both
readings pass through {name GebLean.Ramified.objToNat}`objToNat`'s carrier-copy identification,
needed because a tower sort's denotation does not reduce syntactically to the carrier for a
symbolic tier index.

{docstring GebLean.Ramified.objToNat}

{docstring GebLean.Ramified.ramKappa}

{docstring GebLean.Ramified.ramDeltaIdent}

{docstring GebLean.Ramified.ramKappa_interp}

{docstring GebLean.Ramified.ramDeltaIdent_interp}

This completes the chapter: the higher-order system of Leivant III section 2.3, its auxiliary
coercions at every r-type, and its instantiation over the monadic word algebra
{name GebLean.Ramified.natAlgSig}`natAlgSig` in the section 2.4 ladder whose narrative reading
is Part I chapter 5. The next chapter takes up the characterization built on the syntactic
category this instantiation supplies.
