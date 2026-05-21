# Round-1 adversarial review — erToK via CSLib URM design

Reviewer: fresh-context `general-purpose` Agent (round 1).
Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).

Author response convention: each finding is followed by a
single-line `**Response:**` entry recording one of `fix`,
`defer-with-rationale`, or `reject-as-cosmetic-taste`
(cosmetic only). Per
[`docs/process.md` § Adversarial review](../../process.md),
blocker and serious findings cannot be deferred without an
explicit out-of-scope rationale that withstands a later
adversarial round.

## Verification log

**CSLib URM instruction set (spec §2.1, §5, §6).** Verified
at `.lake/packages/cslib/Cslib/Computability/URM/Defs.lean:44-49`:
`Instr` is exactly `Z n | S n | T m n | J m n q`. `Regs :=
ℕ → ℕ` is confirmed at `Defs.lean:103`. The master-design
primitives `decReg`, `gotoInstr`, `stop` are indeed absent
from CSLib. The spec's emulation strategy (§2.1 table) is
consistent with CSLib's API. `State.init` (line 171)
initialises inputs at registers 0, 1, …, k−1, which clashes
with the spec's reserved-register layout (output at 0, Z0
at 1, inputs at 2..a+1); the spec sidesteps this by using
a custom `initState` rather than `Cslib.URM.State.init`,
but never formally defines `initState`.

**CSLib `noncomputable` boundary (spec §2.1, §10).**
Verified at
`.lake/packages/cslib/Cslib/Computability/URM/Execution.lean:207-232`
that `evalState` and `eval` are both `noncomputable` and
use `Classical.choose` / `Classical.choose_spec`. Verified
at
`.lake/packages/cslib/Cslib/Computability/URM/StraightLine.lean:103-117`
that `straightLine_finalState` and `straightLine_finalRegs`
are `noncomputable` and use `Classical.choose`. The
Prop-valued `Step` and `Steps` (`Execution.lean:58-79`) are
inductive Prop relations, constructive.
`Step.deterministic` (`Execution.lean:86`) uses `grind`
only. `Step.preserves_register` (`Execution.lean:96-105`)
is by case-analysis on the inductive `Step`.
`Steps.eq_of_halts` (`Execution.lean:155-163`) depends on
`step_confluent` → `RightUnique.toConfluent` → mathlib's
`ReflTransGen.total_of_right_unique`, which is purely
inductive. None of these use `Classical` in their stated
proofs, but `lean_verify` could not confirm via
`#print axioms` because CSLib uses Lean 4's `module`
system, which blocks `#print axioms`.

**Existing kToER infrastructure (spec §3).** All claimed
reusable modules and names exist:

- `Nat.tuplePack`, `Nat.tupleAt`, `tuplePackCoef`,
  `tuplePack_le` at
  `GebLean/Utilities/Tupling.lean:34,46,58,164`.
- `Nat.simRecVec`, `Nat.simRec`, `simRecVec_le_of_dominates`
  at `GebLean/Utilities/SimRec.lean:40,52,84`.
- `ERMor1.A_one`, `A_one_iter`, `A_two_iter` (alias
  `towerER`) at
  `GebLean/Utilities/ERAMajorants.lean:53,79,141`.
- `tower` at `GebLean/Utilities/Tower.lean:17`;
  `tower_succ_pow_bound`, `tower_succ_pow_bound_strong`,
  `polynomial_iter_tower_bound` at
  `GebLean/Utilities/ComputationalComplexity.lean:348,399,483`.
- `KMor1.linearBound` at
  `GebLean/LawvereKSimPolynomialBound.lean:207`;
  `KMor1.majorize_by_A_two_iter` at
  `GebLean/LawvereKSimMajorization.lean:699`.
- `Nat.seqPack`, `Nat.seqPackBound` at
  `SzudzikSeq.lean:29` and
  `ComputationalComplexity.lean:82`.
- `kSimSzudzikPackList` at
  `GebLean/Utilities/KSimSzudzikSimrec.lean:31` — **but**
  this is an `ERMor1`-valued combinator, not a K^sim one.
  Spec §3 lists it under "variable-length sequence packing
  in ER and K^sim", inaccurate.
- `ERMor1.simultaneousBoundedRec` at
  `GebLean/Utilities/ERSimultaneousBoundedRec.lean`.

**K^sim level constraint (spec §6, §7, §8.2).**
`KMor1.level` at `GebLean/LawvereKSim.lean:105`: `simrec`
and `raise` each add 1 to the max of children's levels;
`comp` takes max without adding. Pre-existing K^sim atoms
relevant to the spec, with verified levels:

- `KMor1.isZero.level = 1` (`KArith.lean:106`).
- `KMor1.pred.level = 1` (`KArith.lean:72`).
- `KMor1.cond.level = 1` (`KArith.lean:264`).
- `KMor1.eq.level = 2` (`KArith.lean:469`).
- `KMor1.condEq.level = 2` (`KArith.lean:495`).
- `KMor1.mult.level = 2` (`KArith.lean:351`).
- `KMor1.monusSwapped.level = 2` (`KArith.lean:398`).
- `KMor1.pow2.level = 2` (`KArith.lean:537`).

`KMor1.natPair`, `natUnpair`, `tuplePack`, `tupleAt` do not
exist in K^sim. The spec's level-2 simulator claim depends
on these constructions, and the spec puts them out of scope
in §14 while §6 treats them as available.

**Tourlakis §0.1.0.17(c) realisation.** `KMor1.pow2` is
realised at `KArith.lean:500` with level 2. The spec §3's
parenthetical "2^x ∈ K^sim_2 already factors through `kToER`
and `ERMor1.towerER`" is wrong direction: `pow2` is directly
a K^sim term; `towerER` is an ER term unrelated to the K^sim
realisation of 2^x.

**Tourlakis §0.1.0.17(6) `switch` (spec §6.3).** The
repository has `KMor1.cond` (`KArith.lean:222`), a 3-input
binary switch at level 1. An n-ary switch (`kSimSwitch`) as
described in §6.3 is new work. The spec does not specify
the construction.

**`urmLoop` template correctness (spec §4.3).** Traced the
template by hand: starting with B = counter, the
unconditional jump skips body, the head tests `B == 0`, on
false enters body, then decrements B, falls back through
to head. For counter `n`, this runs the body exactly `n`
times with B taking values `n, n−1, …, 1` at successive
body entries. The body has no access to a "current i"
counter. Additionally, the template requires the body
never to write to register `B`; the spec does not establish
or document this non-interference contract on `body`.

**CSLib `Classical.choice` leak (spec §12.8).** Source
inspection suggests `Step.deterministic`, `Steps.eq_of_halts`,
`Step.preserves_register`, `step_confluent`,
`isHalted_iff_normal` are constructive in their stated
proofs. `lean_verify` is not executable against these
because CSLib's files use `module`, blocking
`#print axioms`. The spec's §12.8 obligation as written is
not executable.

**Master-design alignment.** Master design §15 punch list
contains 16 items; §15.1–§15.11 (generic) plus §15.12–§15.16
(Path-2 kToER, closed). Spec §12 introduces 10 punch-list
items but does not cover §15.6 (per-URM construction
matches Tourlakis) or §15.7 (catalogue obligations local),
both of which apply to erToK.

**Internal-document paths.** All cited internal paths exist.

**`scripts/check-axioms.sh` allowlist.** `Classical.choice`
is NOT in the allowlist. Any transitive dependence on
`Classical.choice` is a failure unless individually
annotated.

## Findings

### Blocker

#### B1. §6 simulator level claim contradicts §14's out-of-scope declaration

§6.1 says encoding/decoding of the URM state are realised
as K^sim named composites built from `kSimSzudzikPackList`
or `tuplePack`. §6.2 says per-instruction step functions
use a "repack via `tuplePack`". §14 lists "K^sim-side
`tuplePack`/`tupleAt` named composites" as out of scope,
with the gloss that unpacking goes "via existing
`kSimSzudzikPackList` / `tupleAt` ER analogues composed
with `kToER`". This is internally contradictory: the
simulator must be a `KMor1` (a K^sim syntactic term); it
cannot delegate its register-extraction step to ER terms
transported via `kToER`, both because (a) such a route
makes the erToK side load-bearingly depend on
`LawvereKSimER`, contradicting §12.10's independence claim,
and (b) `kSimSzudzikPackList` returns `ERMor1`, not
`KMor1` (`GebLean/Utilities/KSimSzudzikSimrec.lean:31`).

Fix: either (i) commit to building K^sim-side
`natPair`/`natUnpair`/`tuplePack`/`tupleAt` named composites
in this spec (with explicit constructions and verified
levels), and remove them from the §14 out-of-scope list;
or (ii) replace the encoding with one that uses only
existing K^sim atoms (e.g., raw `simrec` of
`KMor1 (a + |regs| + 1)`-shaped families with parameters
held in argument positions rather than packed). The spec
must pick one, not both.

**Response:** fix (option (i)). Commit to K^sim-side
pairing and tupling, add §6bis subsection with explicit
constructions and level proofs, drop from §14. Necessary
because option (ii) inflates the simrec's argument arity
to `a + maxRegister + 1` and forces the per-instruction
step to manipulate `Fin (a + maxRegister + 1)`-indexed
data — much harder to certify level ≤ 1.

#### B2. Encoding-level construction missing

Even granting B1's fix path (i), the new K^sim-side
`tuplePack`/`tupleAt` composites must come with a verified
level bound. Tourlakis-style Szudzik pairing involves
`Nat.pair` which is built from `succ` and `mult` (or
`succ` and a custom polynomial); `mult` is level 2
(`KArith.lean:351`). If `natPair` is built using `mult`,
it inherits level 2; the outer simrec(time) then adds +1
→ level 3, exceeding the §8.2 claim. The spec does not
show a level-≤-1 construction for `natPair`, nor for
`tuplePack k` for arbitrary `k`.

Fix: commit to specific K^sim definitions for `natPair`,
`tuplePack k`, `tupleAt k i`, and `natUnpairFst` /
`natUnpairSnd`, give level proofs, and reconcile with the
outer simrec's +1 budget.

**Response:** fix. The arithmetic forces a structural
rethink — either an encoding that fits level ≤ 1, or a
different simulator shape. Likely answer: state encoding
uses K^sim `simrec` *inside* the construction of
`tuplePack`/`tupleAt` (so they themselves are level 2);
then the outer time-iterating simrec is a level-2 simrec
whose step function is at level ≤ 1, with the encoding
pre-computed *outside* the simrec at the input level (the
input is already encoded by `encodeInitialState` at level
≤ 2 before the simrec runs). The step function reads
single packed bits via level-1 operations (bit-extraction
in K^sim_1, e.g. via `KMor1.cond` chains and `monus`),
avoiding `mult` inside the step.

Detailed construction goes in §6bis. The simulator's
level then is: outer simrec at level 2, step at level ≤ 1,
total ≤ 2 by `KMor1.level`'s `simrec` rule. The pre-
encoding at level ≤ 2 composes outside the simrec without
adding (since `comp` takes max).

#### B3. Per-instruction `J m n q` step's level is unbounded by spec

§6.2's `kSimSubrJ (m n q : ℕ) : KMor1 1` is parameterised
over arbitrary `m, n`. The general "regs[m] = regs[n]"
test is `KMor1.eq`-shaped, level 2 (`KArith.lean:469`).
The compiler only ever emits `J m Z0 q` (§2.1, §4.4), so
a level-1 step using `KMor1.isZero` suffices in practice —
but the simulator as specified takes any
`Cslib.URM.Program`, not just compiler-emitted ones. If
the simulator handles general `J m n q`, level rises to
2 inside the step, plus the simrec +1 → 3.

Fix: either specialise `kSimSubrJ` to a constrained form
(`kSimSubrJZ0 m q` for `J m Z0 q`) and certify the
compiler only emits this form, or accept the level-2 step.

**Response:** fix. Restrict the simulator to programs
satisfying a `JumpsAreZeroTest` predicate (every `J m n q`
in the program has `n = 1`, i.e. tests against `Z0`).
Compiler `compileER` emits only such programs (per §4.4's
reserved-register invariant); the simulator's
type-signature carries the predicate as a hypothesis.
`kSimSubrJ` becomes `kSimSubrJZ0 (m q : ℕ) : KMor1 1` at
level ≤ 1 using `KMor1.isZero`.

This means the simulator does NOT cover arbitrary CSLib
programs — only programs in our reserved-register layout.
That's exactly what we need for erToK; reword the
simulator's signature accordingly.

#### B4. Internal contradiction §6.1 ↔ §14 about route through `kToER`

§14's "the unpacking is realised via existing
`kSimSzudzikPackList` / `tupleAt` ER analogues composed
with `kToER`" directly contradicts §12.10's claim that
"the erToK side imports no module from the kToER side's
load-bearing path".

Fix: remove the §14 escape clause; commit to a K^sim-native
encoding (see B1, B2).

**Response:** fix. Deleted in tandem with B1's fix; §14
no longer routes through `kToER`.

### Serious

#### S1. §6.1's "stays in K^sim_1 for the bound expression" is wrong

§6.1 claims the encoded-state bound expression is
"polynomial in inputs at each fixed program and stays in
K^sim_1 for the bound expression (multiplication-free
polynomial of fixed degree)". A polynomial of degree `2^k`
is NOT multiplication-free — evaluating `(M+1)^{2^k}`
requires repeated multiplication, which is level 2.

Fix: drop the level-1 claim. State the bound expression's
level as ≤ 2 (matching the simulator's overall budget) and
verify in §7 that the bound composes correctly.

**Response:** fix. Per the B2 response, the bound
expression itself lands in K^sim_2 (uses `mult` and the
`pow2`/`towerK` family). The encoding-bound is part of
`boundExprK`, not a separate object; its construction is
absorbed into §7.1's table.

#### S2. §3's claim that 2^x "factors through `kToER` and `ERMor1.towerER`" is incorrect

`KMor1.pow2 : KMor1 1` is directly defined in K^sim
(`KArith.lean:500`), level 2. The path through ER +
`towerER` is unnecessary and forbidden by §12.10.

Fix: replace the §3 bullet with: "K^sim_2 directly
contains `pow2 ∈ K^sim_2`
(`GebLean/Utilities/KArith.lean::KMor1.pow2`); the K^sim
runtime bound builds on this directly."

**Response:** fix as recommended.

#### S3. `urmLoop` body non-interference contract unspecified

§4.3's `urmLoop` template depends on register B being
preserved by the body. If the body writes to B, the loop
count is wrong. The spec gives no constraint on the body's
`URMComputes` to forbid writing to B, nor does it specify
which scratch registers `urmDecToReg` uses.

Fix: add a contractual precondition on the body's
`URMComputes`: a `writesTo : Finset ℕ` field disjoint from
`{Z0, B, scratch slots used by urmDecToReg}`, established
via `Instr.writesTo` (`Cslib/Computability/URM/Defs.lean:64`)
aggregated over instructions. Document `urmDecToReg`'s
scratch register assignment (allocate a single fresh
register `S` immediately above the body's `maxRegister`).

**Response:** fix. Extend `URMComputes` (§4.2) with a
`writesTo : Finset ℕ` field — Lean-computable from
`P.instrs.map Instr.writesTo` aggregated as a Finset.
Add a `disjoint_writesTo` precondition to `urmLoop`'s
combinator builder. Specify scratch-allocation strategy
in §4.3.

#### S4. `initState` is undefined

§4.2 uses `initState v inputRegs` in the `URMComputes.correct`
field but the spec never defines this function. CSLib's
`State.init` puts inputs at registers 0..k−1, clashing
with §4.4's layout.

Fix: define `initState` explicitly as:

```lean
def initState (v : Fin a → ℕ) (inputRegs : Fin a → ℕ) :
    Cslib.URM.State :=
  ⟨0, fun r => if h : ∃ i, inputRegs i = r then v h.choose else 0⟩
```

(or a constructive equivalent using `Fin.find`).

**Response:** fix. Use the constructive `Fin.find` form
to avoid `Classical.choose` in the definition. Note this
is a definition, not a theorem; even if `Fin.find` returns
`Option (Fin a)`, the data structure is computable.

#### S5. `kSimSwitch` construction unspecified, conflating level claims

§6.3 says `kSimSwitch` is "a chain of bounded recursions
plus equality tests" at level 1. Equality tests
(`KMor1.eq`) are level 2; a level-1 construction is
possible using a `cond` + `pred` chain. The spec doesn't
say so.

Fix: specify the construction precisely (inductive recipe
with a level-1 proof outline).

**Response:** fix. Define in §6bis:
`kSimSwitch_nil default ≡ default`,
`kSimSwitch_cons c cs default arg₀ arg₁ ≡ KMor1.cond
(KMor1.isZero arg₀) c (kSimSwitch cs default (pred arg₀)
arg₁)`. Level: `cond` is level 1, `isZero` level 1, `pred`
level 1; chain of compositions stays at level 1 (max).

#### S6. CSLib axiom verification (§12.8) is not currently executable

CSLib's modules use `module`, blocking `#print axioms`.

Fix: replace §12.8's obligation with one that is
executable. Create a non-module wrapper file
`GebLeanTests/Axioms/URMAxiomCheck.lean` that imports
CSLib and emits `#print axioms` against the named lemmas;
run as part of pre-commit checklist.

**Response:** fix. Rewrite §12.8 to specify the wrapper-
file approach. Add a §11 step E0.5 task: build
`GebLeanTests/Axioms/URMAxiomCheck.lean` early to ensure
CSLib's lemmas we depend on are `Classical.choice`-free
(or document any unavoidable usage at that point).

#### S7. Master-design §15.6 (per-URM construction) silently dropped

Master design §15.6 obliges the adversary to verify
Tourlakis's proof uses per-program URMs and that the spec
preserves this. The spec §12 doesn't enforce it.

Fix: add a §12.11 item mirroring master §15.6, with a
trace obligation across `compileER`, `simulateInKSim`,
`erToK`.

**Response:** fix. Add §12.11.

#### S8. Master-design §15.7 (catalogue obligations local) silently dropped

Without this, a plan-writer could introduce a global
dominance argument later.

Fix: add §12.12 mirroring master §15.7.

**Response:** fix. Add §12.12.

#### S9. §6.3's per-program step level claim is not derivable from the spec as written

§6.3 claims "max of the per-instruction-step levels (each
≤ 1), so ≤ 1", but this hinges on the unresolved B2/B3.

Fix: defer this claim until B2/B3 are resolved.

**Response:** fix. After B2/B3 resolutions, restate the
claim with the §6bis level proofs as supporting evidence.

#### S10. `Halts.toStandardForm_iff` (cited in §12.8) — confirm exact identifier

Confirm `Cslib.URM.Halts.toStandardForm_iff` exists with
that exact spelling, or correct the reference.

**Response:** fix. Verified at
`.lake/packages/cslib/Cslib/Computability/URM/StandardForm.lean:196-198`
the name is `Halts.toStandardForm_iff` inside `namespace
Cslib.URM`. The fully qualified form is
`Cslib.URM.Halts.toStandardForm_iff` — correct as stated.
But §12.8 will be rewritten per S6, so the listing
becomes moot in the new wrapper-file approach.

### Minor

#### M1. §3 bullet for `kSimSzudzikPackList` mislabels its category

The combinator returns `ERMor1`. Relabel as "ER-side
combinator used in `kToER`'s K^sim-to-ER translation".

**Response:** fix as recommended.

#### M2. §4.1's `runFor` is described but not defined

A plan-writer must guess the recursion shape.

Fix: include the definition body inline (≤ 10 lines).

**Response:** fix. Inline definition in §4.1.

#### M3. §4.2's `URMComputes` `inputRegs_inj` field's purpose is unmotivated

Document where injectivity is used.

**Response:** fix. Add one sentence noting that
injectivity ensures `initState`'s definition is
unambiguous and that input slots don't collide.

#### M4. §5.1 table's `tH` values are unspecified for combinators

Add a worked example showing how the tower height reaches
the height-fixing regime (h ≥ 2).

**Response:** fix. Add a paragraph after §5.1 working
through `urmSubrBsum` as the canonical case.

#### M5. §6.3's `kSimSwitch` ambient default value semantics is not specified

Specify the default's interp obligation.

**Response:** fix. After S5's reconstruction in §6bis,
the default is the identity on the encoded state (state
passes through unchanged when PC is past program length —
matching the implicit halt semantics).

#### M6. §7.1 table's `linearBound` wrapper unclear

Clarify the wrapper.

**Response:** fix. `linearBound` data
`(c, d) : ConstantOrShiftedProj × ℕ` wraps into a
`KMor1 a` via the `K_A_one_iter r` named composite where
`r` is derived from `(c, d)` per the kToER side's
`linearBound_le_A_one_iter` (`LawvereKSimMajorization.lean`).
The K^sim runtime bound uses this same translation lemma.

#### M7. §10's grep regex coverage

Confirm; `_final` prefix matches both. No change needed.

**Response:** reject-as-cosmetic-taste (verified
correct).

#### M8. §13.3 missing `Steps` notation citation

Extend the `Execution.lean` bullet to mention the scoped
notations.

**Response:** fix.

#### M9. §3.1 bullet's polynomial-bound formula is informal

Cite the theorem name `Nat.tuplePack_le`.

**Response:** fix.

#### M10. §11 step-decomposition's "critical path: E0 → E1 → E3 → E4" omits E2

Justify or list both candidate critical paths.

**Response:** fix. List both candidates and note that
E2's substantial scope (per-instruction subroutines, PC
dispatch, state-encoding K^sim composites — now expanded
under §6bis per B1/B2 responses) likely makes E2 the
critical path. Re-evaluate after the §6bis content
lands.

#### M11. §9.1's dependency graph ASCII art is ambiguous

Redraw or render in dot.

**Response:** fix. Redraw as a clean dot block.

### Cosmetic-taste

#### C1. §1's "is **out of scope here**" uses bold for emphasis

Per `CLAUDE.md` style, drop the bold.

**Response:** fix.

#### C2. §2.1 table mixes imperative and noun phrases inconsistently

**Response:** fix. Use noun phrases uniformly ("direct
match"; "emulation via …"; "addition of …").

#### C3. §3 bullet ends with "factors through `kToER` and `ERMor1.towerER`"

Subsumed by S2's fix.

**Response:** fix (via S2).

#### C4. §4.3's `urmIf` template uses label-style placeholder text

Document the pseudo-code convention.

**Response:** fix. Add a one-line preamble noting that
`elseLabel`, `endLabel`, `loopHead`, `bodyHead` are
PC-offset placeholders resolved by `shiftJumps` at
combinator-assembly time.

#### C5. §5.1's table column "stepBound shape" mixes Big-O with literal expressions

Choose one convention.

**Response:** fix. Use literal Lean-`Nat` expressions
throughout (`1`, `v 1 + 1`, etc.), since `URMComputes.stepBound`
is itself a `Fin a → ℕ` function — no asymptotic
suppression is needed.

#### C6. §6.1's "pairCoef" undefined

Should be `tuplePackCoef`.

**Response:** fix. (Or define `pairCoef` explicitly as
the special case `tuplePackCoef 0 = 1` after Szudzik
pair.)

#### C7. §7.1's table caption lacks a column header

Clarify it's an upper bound.

**Response:** fix.

#### C8. §8.1's code block uses `![...]` while earlier sections use `Fin` lambdas

Converge on one notation.

**Response:** fix. Use `Fin` lambdas throughout (matches
the kToER side's prevailing convention).

#### C9. §9.1's dependency-graph caption omits the §1 out-of-scope qualifier reminder

**Response:** fix.

#### C10. §11's "Substantial cycle" / "Medium cycle" are value-laden

Quantify.

**Response:** fix. Replace with estimated SLOC bands
(e.g., "~300–600 lean lines", "~150–300 lean lines") and
expected adversarial-review-round count from prior
cycles.

#### C11. §2.1's "(noncomputable)" appears twice in the table's last row

Tighten.

**Response:** fix.

## Convergence assessment

This round does NOT converge: 4 blocker(s), 10 serious
finding(s).

The dominant defect cluster is the K^sim-side encoding of
the URM state: the spec depends on `tuplePack` / `tupleAt`
/ `natPair` / `natUnpair` realised in K^sim (§6.1–§6.2)
while declaring those constructions out of scope (§14) and
routing them via `kToER` in violation of §12.10's
independence claim. The spec must either commit to the
K^sim-native encoding (with level proofs that fit the
level-2 budget) or refactor the simulator to avoid packed
state. The level-2 claim of `erToK` (§8.2) cannot be
evaluated until this is settled.

A secondary cluster concerns CSLib semantic detail not
reflected accurately: `KMor1.eq` is level 2 (so `J m n q`
for arbitrary `m, n` forces the per-instruction step to
level 2, not 1); `2^x` is realised directly in K^sim, not
through `kToER`; and the §12.8 axiom-check obligation is
not currently executable against CSLib's `module`-style
files.

A tertiary cluster involves the `urmLoop` template's body
non-interference contract on register `B` and unspecified
scratch registers (§4.3), and the silent dropping of
master-design punch-list items §15.6 and §15.7.
