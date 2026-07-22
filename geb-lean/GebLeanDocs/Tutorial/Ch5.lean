import VersoManual
import GebLeanDocs.Bibliography
import GebLean.Ramified.Examples

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

/-! # The section 2.4 ladder

Part I chapter 5 of the ramified-recurrence manual. See
`docs/superpowers/specs/2026-07-22-verso-ramified-manual-design.md`
section 4.1.
-/

#doc (Manual) "The section 2.4 ladder" =>

Chapter 4 presented the ramified schema as a general mechanism; this chapter works
Leivant III section 2.4's ladder of examples over the monadic word algebra
{name GebLean.Ramified.natAlgSig}`natAlgSig`, the `1 + X` algebra of the unary
naturals {citep leivant3}[]. Each example below is a schema identifier paired with an
interpretation lemma stating what it denotes on the standard carrier; every lemma is
proved in `GebLean/Ramified/Examples.lean` and stated here without proof, to exhibit
the semantics rather than establish it.

# The coercions

Leivant III section 2.4(1) supplies two downward coercions between {tech}[object
type]s, both extensionally the identity on the carrier. This development instantiates
them over the tower-sort chain of {tech}[tier]s that chapter 3 built.

{name GebLean.Ramified.ramKappa}`ramKappa` is the single {tech}[`Omega`-type]-lowering
step, from `RType.tower (m + 1)` to `RType.tower m` for a natural number `m`: `kappaHatIdent`
(`GebLean/Ramified/OmegaShift.lean`) instantiated at the object type `RType.tower m`, an
identifier whose recurrence reconstructs its argument constructor by constructor.
{name GebLean.Ramified.ramDeltaIdent}`ramDeltaIdent` composes `ramKappa` at every step
from `RType.tower m` down to `RType.o`, an `m`-fold composite lowering a tower sort all
the way to the base object sort.

Both interpretation lemmas record that these coercions denote the identity on the
carrier. {name GebLean.Ramified.ramKappa_interp}`ramKappa_interp` reads the denotation of
`ramKappa m` on an environment `ρ` at context `[RType.tower (m + 1)]` as the numeric
reading of `ρ 0` at the lower tower sort;
{name GebLean.Ramified.ramDeltaIdent_interp}`ramDeltaIdent_interp` reads the denotation
of `ramDeltaIdent m`, directly by `freeAlgToNat` since its result sort is `RType.o`, as
that same numeric reading of `ρ 0`. Both readings pass through the carrier-copy
identification a tower sort carries, since its denotation does not reduce syntactically
to the carrier for a symbolic `m`.

# Addition and multiplication

Leivant III section 2.4(2) defines addition and multiplication by monotonic recurrence
over `natAlgSig`'s single unary constructor. {name GebLean.Ramified.ramAdd}`ramAdd`, at
context `[RType.o, RType.omega RType.o]` and result `RType.o`, recurs on the second
argument with the first as {tech}[recurrence parameters]: `a + 0 = a` and
`a + (n + 1) = (a + n) + 1`. {name GebLean.Ramified.ramMul}`ramMul`, at context
`[RType.omega RType.o, RType.omega RType.o]` and result `RType.o`, recurs on the second
argument with the first — itself at `RType.omega RType.o` — as parameter: `x * 0 = 0`
and `x * (n + 1) = x * n + x`, the inner addition supplied by `ramAdd` through a hole.

{name GebLean.Ramified.ramAdd_interp}`ramAdd_interp` states that on natural-number
inputs `a` and `b` the denotation of `ramAdd` reads out as `a + b`.
{name GebLean.Ramified.ramMul_interp}`ramMul_interp` states the corresponding fact for
`ramMul`: on inputs `x` and `y` the denotation reads out as `x * y`.

# The size function

Leivant III section 2.4(6) defines a size function `sz`, presented here ahead of
exponentiation because it is, like addition and multiplication, first-order: its
recurrence argument sits at `RType.omega RType.o` and its recursive results at
`RType.o`. {name GebLean.Ramified.ramSize}`ramSize`, at context `[RType.omega RType.o]`
and result `RType.o`, is the monotonic recurrence with no parameters: `sz (0) = 0` and
`sz (n + 1) = sz (n) + 1`. Over the `1 + X` word algebra a recursive result rebuilds the
count of its subterm at each step, so the recurrence is extensionally the identity; the
paper's exact typing for `sz` was not independently verified, and the shape adopted here
follows the schema's general monotonic form.

{name GebLean.Ramified.ramSize_interp}`ramSize_interp` states this identity: for a
carrier element `t`, the denotation of `ramSize` on the environment carrying `t` reads
out, by `freeAlgToNat`, as the count of `t` itself.

# Exponentiation, the ladder's turn

Leivant III section 2.4(3) defines an exponentiation `e` by second-order recurrence,
the ladder's turn. Every identifier above recurses at an {tech}[object type] and
produces a value at an object type; `e` recurses at the function type `ramFun`, the
r-type `RType.arrow RType.o RType.o`. Its recursive results are values of `ramFun`,
functions `RType.o → RType.o`, rather than elements of `RType.o`, and its recurrence
argument sits at `RType.omega ramFun` — one {tech}[tier] above the output `ramFun`,
{name GebLean.Ramified.RIdent.mrec}`RIdent.mrec`'s indexing exactly as chapter 4 stated
it. Recursing at a function type rather than an object type is what buys exponentiation
from iteration.

{name GebLean.Ramified.ramExp}`ramExp`, at context `[RType.omega ramFun]` and result
`ramFun`, is the recurrence `e (0) = sc` and `e (n + 1) = e (n) ∘ e (n)`, where `sc` is
the successor wrapper and `∘` is two-fold application, each supplied as an
explicit-definition identifier filling a hole. Self-composing the recursive result at
every step, rather than applying the step function once more to it, is what turns
`2^n`-fold repetition of the successor into `2^{n+1}`-fold repetition rather than
`(n + 1)`-fold.

{name GebLean.Ramified.ramExp_interp}`ramExp_interp` states the resulting semantics:
for a recurrence argument `ρ 0` at `RType.omega ramFun` and an input `x`, the denotation
`(ramExp.interp ρ) x` has count `freeAlgToNat x + 2 ^ freeAlgToNat (ρ 0)` — the
`2 ^ (count (ρ 0))`-fold iterate of the successor applied to `x`.

# The `2_m` ladder

Leivant III section 2.4(4) iterates `e` to build the ladder `2_m` that chapter 2
forward-referenced: `2_0 (x) = x` and `2_{m+1} (x) = 2 ^ (2_m (x))`. No identifier
realizes this iteration directly: the tier discipline forbids a raising coercion
`RType.o → RType.omega ramFun` — no identity-realizing coercion into a strictly higher
tier exists — so the `m`-fold composite of `e` cannot be assembled as a single schema
identifier whose recurrence argument is itself the output of a previous stage.
{name GebLean.Ramified.ramTwoPow}`ramTwoPow` instead composes, at the carrier level,
`m` applications of the single exponential step `e (x) (0) = 2 ^ x` obtained by driving
`ramExp` with `x` and evaluating the result at `0`.

{name GebLean.Ramified.ramTwoPow_interp}`ramTwoPow_interp` states that on a carrier
element `x`, the count of `ramTwoPow m x` equals `GebLean.tower m (freeAlgToNat x)`,
the height-`m` tower of twos (`GebLean/Utilities/Tower.lean`) applied to the count of
`x`. This is the fact chapter 2 promised: the schema's unrestricted nesting reaches
every level of the tower, realized here as the `m`-fold iteration of the single
second-order recurrence `ramExp`.
