# Master design — ER ↔ K^sim_2 categorical equivalence via URM simulation

> **Status.** Step 0 master design. Awaits adversarial review and
> user sign-off before per-step cycles begin.
>
> **Position in the project.** Supersedes the direct-translation
> `kToER` strategy (preserved as renamed `kToERDirect` /
> `kToERNDirect` infrastructure with proven level-0 and level-1
> dominance results) per the architectural pivot recorded in
> `docs/research/2026-05-02-ksim-to-er-architectural-pivot-handoff.md`.
> Provides the master structure within which twelve subsequent
> brainstorm + writing-plans + adversarial-review cycles execute,
> closing both `kToER` and `erToK` directions on a shared URM
> kernel.

---

## §1 Status and motivation

### §1.1 What the prior strategy attempted

The direct-translation `kToER : KMor1 → ERMor1` (now renamed
`kToERDirect`) translated each K^sim morphism to an `ERMor1` term
by structural recursion. The simrec case used
`ERMor1.boundedRec base step bound` with a bespoke
`kSimTowerBound` ER expression giving a pointwise tower-of-
exponentials bound on the K^sim function value. Five plan
iterations attempted to discharge the dominance theorem
`kSimTowerBound_dominates_inline`. All failed at related load-
bearing claims (impossible PolyBound assumptions, false bounds at
level-1 children, glossed `Nat.rec` ↔ `Nat.iterate` bridges, false
absorption inequalities involving a `3^E` coefficient field).

### §1.2 Why the strategy was misaligned with the literature

The published proofs of the elementary-recursive ↔ K^sim
equivalence (notation: Tourlakis 2018 §0.1.0.44,
`K^sim_n = E^{n+1}` for n ≥ 2; the `E^{n+1}` here is the
Grzegorczyk-hierarchy notation that the literature uses
interchangeably with our `ERMor1` formalization at n+1 = 3 —
see §1.4) do not construct an ER expression that bounds the
K^sim function's value pointwise. They route through
register-machine simulation: Tourlakis's §0.1.0.44 reduces
to §0.1.0.43 (Ritchie–Cobham property) and §0.1.0.15
(`K^sim_n = L_n`). Ritchie–Cobham, in our project's
terminology, states that a function is in ER iff it is
computable on some URM with runtime bounded by an ER
expression. The bound is on URM *runtime*, not on the
function's *value*.

The asymmetry of the project's prior strategy is also visible:
the `erToK` direction had been designed via URM simulation per
Appendix A of `docs/lawvere-k-sim-hierarchy.md`, whereas
`kToERDirect` used direct categorical translation. Symmetric
literature alignment requires URM simulation in both directions.

### §1.3 What this design closes

A URM kernel definition with Tourlakis's six primitive
instructions (cited Tourlakis 2018 §0.1.0.43 proof, p. 19);
catalogues of URM subroutines emulating each ER and K^sim
constructor and of ER and K^sim subroutines emulating each URM
primitive; per-program compilers and per-URM simulators
constructed as one-line `match` over source-language constructors
or URM instructions; runtime-bound bookkeeping via a
`URMComputes` structure carrying a Lean step-bound function plus
a tower-witness; functor liftings; strict categorical
isomorphism `LawvereERCat ≅ LawvereKSimDCat 2` packaged as a mathlib
`Equivalence`.

### §1.4 What "ER" means in this project, and what it does not

This project formalizes a specific construction of the
elementary-recursive functions:

- The morphism inductive `ERMor1` with constructors `zero`,
  `succ`, `proj`, `sub`, `comp`, `bsum`, `bprod` (per
  `GebLean/LawvereER.lean`), matching Wikipedia's
  elementary-recursive-function definition.
- The categorical packaging `LawvereERCat` (objects `ℕ`,
  morphisms quotients of `ERMor1` by extensional equality of
  interpretations).

The literature commonly characterizes the same function class
as `E^3`, the third level of the Grzegorczyk hierarchy. The
two are provably equivalent — the same total functions on `ℕ`
arise — but are constructed quite differently: the
Grzegorczyk hierarchy is built iteratively, with each level
`E^{n+1}` obtained from `E^n` by closing under bounded
recursion using a level-`n` bounding function. **This
project does not formalize the Grzegorczyk construction, and
every step in the proof chain below uses ER directly without
invoking the ER ↔ E^3 equivalence as a logical dependency.**

Throughout this design, when literature citations refer to
`E^n` or `E^3` (notably Tourlakis 2018 §0.1.0.27, §0.1.0.43,
§0.1.0.44), those references are used for the proof
**structure** that they exhibit (URM simulation, runtime
bound shape, hierarchy correspondence) — not as logical
dependencies. Concretely: every claim of the form "this
expression is in `E^n`" in the literature is replaced in our
proof by "this expression is in `ER`" by direct construction
in our `ERMor1` inductive plus its named composites
(`pred`, `discN`, `boundedRec`, etc., per `Utilities/ERArith.lean`
and `LawvereERPolynomialBound.lean`). The cited literature
guides what to construct; the constructions live entirely
inside our `ERMor1` formalization.

The bound shape `tower h (linear of inputs)` for fixed `h ≤
2` is itself in ER directly: `2^x ∈ ER` (Tourlakis 2018
§0.1.0.17 (c) gives this construction in K^sim, and the same
construction applies in ER using `bsum`/`bprod`-based bounded
exponentiation), iterated `h` times stays in ER by closure
of ER under composition.

### §1.5 What we implement, and what we only borrow as technique

Tourlakis 2018 §0.1.0.43 (Ritchie–Cobham), §0.1.0.44
(`K^sim_n = E^{n+1}`), §0.1.0.27 (bounding lemma), and
§0.1.0.22 (Grzegorczyk hierarchy) are theorems whose Tourlakis
proofs are stated in `E^n` terms. The two directions of
Tourlakis 0.1.0.44 use **different** techniques in the
literature: ⊆ direction (`K^sim_n ⊆ E^{n+1}`) is structural
induction over K^sim levels, using `E^{n+1}`'s closure
under bounded primitive recursion as a definitional fact
plus Tourlakis's `A_n^r` Ackermann-style functions as
majorants. ⊇ direction (`E^{n+1} ⊆ K^sim_n`) goes via
Ritchie–Cobham (URM simulation).

For our project, ER provides closure under bounded
recursion as a **proven theorem** (the `boundedRec` named
composite in `Utilities/ERArith.lean`), so the **structural
⊆ proof transcribes line-by-line** into our ER formalization
without invoking the Grzegorczyk hierarchy. We use this
direct transcription for `kToER`. For `erToK`, we transcribe
Ritchie–Cobham's URM-simulation argument (Appendix A's
design). The two directions therefore use different
techniques in our project, mirroring the literature exactly.

(Historical note: the architectural-pivot handoff document
recommended URM simulation in BOTH directions, claiming
"Tourlakis's proof IS via URM simulation in both
directions". On re-reading Tourlakis 2018 page 22, this is
wrong: only the ⊇ direction uses URM. The ⊆ direction is
structural with bounded recursion. Path 2's split — ⊆
structural, ⊇ URM — is the actual literature pattern.)

#### kToER side (Path 2 — Tourlakis ⊆ structural induction)

What we **implement** (each as a Lean definition with a
Lean correctness theorem, in steps 1–5 of §2):

- Foundational tupling (step 1):
  - `Nat.tuplePack : (k : ℕ) → (Fin k → ℕ) → ℕ` and
    `Nat.tupleAt : (k : ℕ) → ℕ → Fin k → ℕ` (Lean Nat-level
    fixed-length k-tuple Szudzik pairing); pack-unpack
    bijection theorems; polynomial value bound on packed
    tuple.
  - `ERMor1.tuplePack`, `ERMor1.tupleAt` named composites in
    ER, with interp lemmas + `PolyBound` builders.
  - **K^sim-side tuplePack/tupleAt is not needed for Path 2's
    load-bearing chain** and is therefore not built in this
    cycle group. Pairing and projections at level ≤ 2 in
    K^sim do exist — by Tourlakis 2018 §0.1.0.44, `K^sim_2 =
    E^3 ⊇ ER`, and ER contains the pairing function and its
    projections (in fact in E^2 per Tourlakis §0.1.0.34
    proof). A naive K^sim construction (e.g. building Szudzik
    unpair as bounded search whose simrec step uses
    multiplication as a step-function) hits level 3 by an
    obvious approach, but a less naive construction at level
    ≤ 2 must exist by the equivalence we are proving.
    Constructing K^sim-side `tuplePack`/`tupleAt` may turn
    out to be needed for the erToK URM simulator (step 9);
    it is not blocking for the kToER side. The categorical
    iso `(n+1) ≅ 1` on the K^sim side is decorative; the
    `simultaneousBoundedRec` in step 2 needs only ER-side
    tuplePack/tupleAt.
  - Categorical iso `(n+1) ≅ 1` in `LawvereERCat` only
    (decorative, witnessing that ER-side products collapse
    via Szudzik pairing in the morphism quotient).
- Simultaneous bounded recursion in ER (step 2):
  - `ERMor1.simultaneousBoundedRec` — multi-output ER
    bounded recursion at the ERMorN level. Implementation
    packs the (k+1)-tuple of intermediate values internally
    via `Nat.tuplePack`, recurses on the packed state via
    single-output `boundedRec`, unpacks at the end via
    `Nat.tupleAt`. Output is `ERMorN`.
  - Interp lemma + `PolyBound` builder.
- Tourlakis A_n named composites in ER (step 3):
  - `ERMor1.A_one : ERMor1 1` with interp `λx. 2x + 2`
    (Tourlakis 2018 page 22, A_1).
  - `ERMor1.A_one_iter : ℕ → ERMor1 1` with interp
    `A_1^r(x) = 2^r · x + (2^{r+1} − 2)`.
  - `ERMor1.A_two_iter` aliasing existing
    `ERMor1.towerER` (interp = `tower r x` = A_2^r(x)).
  - `PolyBound` builders for `A_one` and `A_one_iter`
    (linear-shape).  No `PolyBound` for `A_two_iter`:
    `tower r x` for `r ≥ 1` is not polynomially bounded
    in `x`, and `ERMor1.PolyBound` is the bprod-free
    polynomial fragment per the structural-towerHeight
    section of `LawvereERPolynomialBound.lean`.  The
    level-2 chain (steps 4–5) uses Nat-level inequalities
    directly, not a PolyBound on `A_two_iter`.
- Majorization theorem (step 4 — Tourlakis 0.1.0.10):
  - `linearBound_le_A_one_iter` translation lemma turning
    any `KMor1.linearBound (c, d)` into `A_1^r` for an
    explicit `r`.
  - `KMor1.majorize_by_A_n_iter`: for every
    `f : KMor1 a` of level ≤ n (n ≤ 2), an explicit
    Lean-`Nat` `r` such that `f.interp v ≤ A_n^r (vMax v)`.
    Proof: structural induction. Reuses existing
    `kToERDirect_linearBound_dominates_level_zero` and
    `_level_one` (composed with the translation lemma) for
    levels 0 and 1; fresh proof at level 2 using
    `simultaneousBoundedRec`'s bound arithmetic.
- `kToER` and `kToERFunctor` (step 5):
  - `kToER : KMor1 a → KMor1.level f ≤ 2 → ERMor1 a`
    defined by structural induction on K^sim. Each
    constructor case is a one-line `match` invoking named
    composites; the simrec case uses
    `simultaneousBoundedRec` with the A_n^r bound from
    step 4.
  - `kToER_interp : (kToER f h).interp v = f.interp v`.
  - `kToERN : KMorN a m → ... → ERMorN a m` and
    `kToERN_interp` (component-wise).
  - `kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat` with
    functor laws.

What we **borrow as technique** (without transcribing Tourlakis's
proofs):

- Tourlakis 2018 §0.1.0.10 majorization-by-`A_n^r`: the
  structural induction's bound shape and per-constructor
  bookkeeping.
- Tourlakis 2018 page-22 ⊆ proof structure: the per-K^sim-
  level closure-under-bounded-recursion argument.

#### erToK side (URM simulation, see §4–§9)

What we **implement**:

- URM kernel and `URMComputes` structure (§4, step 7).
- Composition combinators `urmSeq`, `urmIf`, `urmLoop`
  (§5).
- ER → URM compiler `compileER` and its `URMComputes`
  catalogue entries (§6, §7, step 8).
- K^sim simulator for URM `simulateInKSim` per Appendix A.3
  of `docs/lawvere-k-sim-hierarchy.md` (§7, step 9).
- Runtime bound `boundExprK e` in K^sim_2 (§9, step 10).
- `erToK : ERMor1 a → KMor1 a` of level ≤ 2,
  `erToK_interp`, `erToKFunctor` (§10, step 10).

What we **borrow as technique**:

- Tourlakis 2018 pp. 19-21 worked URM examples and the
  Loop-to-URM template (informs `compileER` and
  `urmLoop`).
- Tourlakis's per-program / per-URM convention (matched
  in §7 by per-URM `simulateInKSim`).
- The K^sim_2 runtime-bound shape via `2^x ∈ K^sim_2` per
  Tourlakis 2018 §0.1.0.17 (c).

#### Strict iso (step 11)

`kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)` and
the reverse, proved directly from `kToER_interp` +
`erToK_interp` plus the morphism-quotient setup. No `E^n`
hierarchy intermediates. Mathlib `Equivalence` derived as a
one-line wrapper.

#### What we do not implement and do not depend on

- Tourlakis 2018 §0.1.0.43 (Ritchie–Cobham) as a standalone
  Lean theorem. For `erToK`, we implement only the URM-
  simulation chain (`compileER` + `simulateInKSim` +
  `boundExprK`); we do not state Ritchie–Cobham as a Lean
  theorem. For `kToER`, Ritchie–Cobham is not used at all.
- Tourlakis 2018 §0.1.0.44 as a standalone Lean theorem
  stating `K^sim_n = E^{n+1}`. The categorical iso (step 11)
  is proven directly.
- Tourlakis 2018 §0.1.0.27 (bounding lemma) as a Lean
  theorem characterizing `E^{n+1}` functions. Our `A_n^r`
  bounds are constructed directly per K^sim term.
- The Grzegorczyk hierarchy at any level. No `E^0`, `E^1`,
  `E^2`, or `E^n` is formalized in this project.
- The ER ↔ E^3 function-class equivalence. The two are
  provably equivalent in the literature but our proof chain
  never uses that fact.

The cycles in §2 each carry this discipline: every Lean
function, definition, and theorem produced is realized
directly in `ERMor1` / `KMor1` / `URMProgram` and their
named composites; no cycle introduces an `E^n` placeholder,
opaque "closure-under-bounded-recursion" lemma over `E^n`,
or any other Grzegorczyk-hierarchy artefact.

---

## §2 The 0–11 cycle structure

Each cycle consists of brainstorming + sequential-thinking +
writing-plans, followed by adversarial brainstorming +
sequential-thinking, iterated until convergence. Per CLAUDE.md's
literature-citation discipline (transcription workstreams),
every planned function, definition, or theorem in the cycle's
plan carries a literature reference; every implemented entity
carries the same reference in its docstring.

The 0–11 cycles split into a kToER side (steps 1–5,
structural-induction Path 2) and an erToK side (steps 6–10,
URM-simulation), with step 11 producing the categorical iso.

### Step 0 — Master design (this document)

Lays out the full structure. Adversarial review obligated to
re-run the prior failure-mode hypotheses (§15) against the
proposal.

### Steps 1–5 — kToER side (Tourlakis ⊆ structural induction)

#### Step 1 — Foundational tupling infrastructure (ER side only)

`Nat.tuplePack`, `Nat.tupleAt`, pack-unpack bijection,
polynomial value bound (`Utilities/Tupling.lean`).
`ERMor1.tuplePack`, `ERMor1.tupleAt`, `PolyBound` builders,
interp lemmas (`Utilities/ERTupling.lean`). Categorical iso
`(n+1) ≅ 1` in `LawvereERCat` (decorative).

K^sim-side tuplePack/tupleAt is omitted from this cycle.
Pairing and projections at level ≤ 2 in K^sim do exist (by
the equivalence `K^sim_2 = E^3` and the fact that ER's
`natPair` is in ER), but the naive K^sim construction —
projection as `λz. μx ≤ z. ∃y ≤ z. J(x,y) = z` whose simrec
step uses `mul ∈ K^sim_2` — pushes the simrec to level 3.
A non-naive construction at level ≤ 2 must exist by the
equivalence we are proving; we expect it is in published
literature on K^sim / loop-program hierarchies. The
`simultaneousBoundedRec` in step 2 needs only ER-side
tupling; K^sim's native multi-output `simrec` constructor
handles K^sim's side. K^sim-side tupling may be needed for
the erToK URM simulator (step 9); if so, it gets built then.

#### Step 2 — Simultaneous bounded recursion in ER

`ERMor1.simultaneousBoundedRec` named composite
(`Utilities/ERSimultaneousBoundedRec.lean`). Multi-output
ERMorN-level interface; implementation packs the (k+1)-tuple
of intermediate values via `Nat.tuplePack`, recurses on the
packed state via single-output `boundedRec`, unpacks at the
end via `Nat.tupleAt`. Interp lemma + `PolyBound` builder.
The packing arithmetic uses Szudzik pairing (already in ER as
named composites). When the per-component bound is itself
polynomially bounded (K^sim levels ≤ 1), the
`PolyBound` builder (`ofSimultaneousBoundedRec`) produces a
polynomial bound on the packed state. At level 2 the
per-component bound is `A_2^r` (tower-fast), so neither it
nor the resulting packed-state bound is a PolyBound; the
level-2 chain uses `simultaneousBoundedRec_interp_correct`
directly with a Nat-level dominance hypothesis. In both
regimes, the kToER outer level sees a clean ERMorN
interface.

K^sim has simultaneous recursion built in (the `simrec`
constructor); no analogous infrastructure is needed on the
K^sim side.

#### Step 3 — Tourlakis A_n named composites in ER

`ERMor1.A_one : ERMor1 1` (interp `λx. 2x + 2`, Tourlakis
page 22 A_1).
`ERMor1.A_one_iter : ℕ → ERMor1 1` (interp `A_1^r`).
`ERMor1.A_two_iter` aliasing existing `ERMor1.towerER`
(interp `A_2^r = tower r`).
`PolyBound` builders for `A_one` and `A_one_iter`
(linear-shape). `A_two_iter` has no `PolyBound`
(tower-fast); the level-2 chain uses a Nat-level
inequality from step 4 instead.
(`Utilities/ERAMajorants.lean`.)

#### Step 4 — Majorization theorem (Tourlakis 0.1.0.10)

`linearBound_le_A_one_iter` — translation lemma turning any
`KMor1.linearBound (c, d)` into an `A_1^r` bound with
explicit Lean-`Nat` `r := max(⌈log_2(c+1)⌉, ⌈log_2(d/2 + 1)⌉)`.

`KMor1.majorize_by_A_n_iter`: for every `f : KMor1 a` of
level ≤ n (n ≤ 2), an explicit Lean-`Nat` `r` such that
`f.interp v ≤ A_n^r (vMax v)`. Proof by structural induction:

- Levels 0 and 1: reuses existing
  `KMor1.linearBound_dominates` (line 507 of
  `LawvereKSimPolynomialBound.lean`) — the bound on
  `f.interp v` directly, applicable to any ER realisation
  of `f` — composed with `linearBound_le_A_one_iter`. The
  prior `kToERDirect_linearBound_dominates_level_*`
  theorems are equivalent under
  `kToERDirect_interp_level_*`'s interp-preservation but
  state the bound on `(kToERDirect f).interp` rather than
  `f.interp`; using `KMor1.linearBound_dominates` is more
  direct.
- Level 2: fresh proof using `simultaneousBoundedRec`'s
  bound arithmetic.

(`LawvereKSimMajorization.lean`.)

#### Step 5 — `kToER` and `kToERFunctor`

`kToER : KMor1 a → KMor1.level f ≤ 2 → ERMor1 a` by
structural induction on K^sim. Each constructor case is a
one-line `match` invoking named composites and
`simultaneousBoundedRec`. The simrec case uses the A_n^r
majorant from step 4 to ensure `boundedRec`'s truncation
does not fire.
`kToER_interp`, `kToERN`, `kToERN_interp`, `kToERFunctor :
LawvereKSimDCat 2 ⥤ LawvereERCat`, functor laws.
(`LawvereKSimER.lean` — the bare name, distinct from
`LawvereKSimERDirect.lean`.)

### Steps 6–10 — erToK side (URM simulation)

#### Step 6 — `RegisterMachine.lean` audit and gap-fill

Audit existing `GebLean/Utilities/RegisterMachine.lean` (166
lines) for sufficiency relative to §4 below. Likely outcome:
small additive lemmas. Near-empty cycle.

#### Step 7 — `URMConcrete.lean`

Define `URMInstr` (Tourlakis's six primitives), `URMProgram`,
`toRegisterMachine`, the `URMComputes` structure (§4.4), and
the composition combinators `urmSeq`, `urmIf`, `urmLoop` (§5)
with both stepBound arithmetic and tower-witness arithmetic.

#### Step 8 — ER → URM compiler

Catalogue `URMSubroutinesER.lean`: URM subroutines
emulating each `ERMor1` constructor (`zero`, `succ`, `proj`,
`sub`, `comp`, `bsum`, `bprod`), each with `URMComputes`.
Compiler `compileER : ERMor1 a → URMProgram` as a one-line
`match`.

#### Step 9 — K^sim simulator for URM and runtime bound

Catalogue `KSimSubroutinesURM.lean`: K^sim subroutines
emulating each URM primitive instruction. Per-URM simulator
`simulateInKSim : URMProgram → KSimMorN ...` using the
catalogue plus PC-dispatch via `switch` and `simrec` over
time. Per Appendix A.3 of `docs/lawvere-k-sim-hierarchy.md`.

Runtime bound for ER → URM compilation: for each
`e : ERMor1 a`, construct `boundExprK e : KMor1 a` of level
≤ 2 with `(compileER e).URMComputes.stepBound v ≤
(boundExprK e).interp v`. Shape: `tower h_e (vMax v +
offset_e)` constructed in K^sim using `2^x ∈ K^sim_2` per
Tourlakis §0.1.0.17 (c).

#### Step 10 — `erToK` and `erToKFunctor`

`erToK : ERMor1 a → KMor1 a` of level ≤ 2 defined as
`simulateInKSim (compileER e) (boundExprK e, projects, zeros)`
followed by output-register projection. `erToKN`,
`erToK_interp`, `erToKFunctor : LawvereERCat ⥤
LawvereKSimDCat 2`, functor laws.
(`LawvereERKSim.lean`.)

### Step 11 — Categorical isomorphism (`LawvereERKSimEquivalence.lean`)

Strict equality `kToERFunctor ⋙ erToKFunctor = 𝟭
(LawvereKSimDCat 2)` and `erToKFunctor ⋙ kToERFunctor = 𝟭
LawvereERCat`. Each holds because both functors preserve
interpretation pointwise, the morphism categories are
quotients by extensional-equality of interpretations, and
both functors are identity on objects. Mathlib `Equivalence`
derived as a one-line wrapper.

### Parallelization

The kToER side and erToK side are independent: step 1 and
steps 6/7 share no dependencies beyond the existing landed
code. Recommended parallel structure:

- Step 1 (kToER tupling) || Step 6 (RegisterMachine audit)
  → Step 7 (URMConcrete).
- Step 2 (simultaneousBoundedRec) requires step 1.
- Step 3 (A_n) is independent of steps 1, 2 but its use in
  step 4 requires it.
- Step 4 (majorization) requires step 1, 2, 3.
- Step 5 (kToER) requires step 4.
- Step 8 (ER → URM compiler) and step 9 (K^sim simulator +
  bound) both require step 7; they can run in parallel.
- Step 10 (erToK) requires steps 8 and 9.
- Step 11 requires steps 5 and 10.

Longest serial chain on the kToER side: 0 → 1 → 2 → 3 → 4 →
5 → 11 (7 cycles). On the erToK side: 0 → 6 → 7 → 8/9 → 10
→ 11 (6 cycles). The kToER side is the critical path.

### Per-step expected size

| Step | Side | Expected size | Notes |
| - | - | - | - |
| 0 | both | substantial | this document |
| 1 | kToER | medium | tupling infra + bijection + bounds |
| 2 | kToER | medium | simultaneousBoundedRec |
| 3 | kToER | small | A_one + iters + aliasing |
| 4 | kToER | substantial | majorization theorem |
| 5 | kToER | medium | structural induction + functor |
| 6 | erToK | empty/small | RegisterMachine audit |
| 7 | erToK | substantial | URM kernel + URMComputes |
| 8 | erToK | substantial | ER → URM compiler + catalogue |
| 9 | erToK | substantial | K^sim simulator + bound |
| 10 | erToK | medium | erToK composition + functor |
| 11 | both | small | strict iso packaging |

---

## §3 Path 2 — kToER via structural induction (Tourlakis 0.1.0.44 ⊆)

This section presents the load-bearing path for `kToER`
(`K^sim_2 ⊆ ER`), following Tourlakis 2018 §0.1.0.44 ⊆
direction line-by-line. The direction uses structural
induction over K^sim levels, with Tourlakis's `A_n^r`
functions as majorants and ER's proven `boundedRec` closure
as the inductive step.

This is **separate from** the URM-simulation infrastructure
in §4–§9, which is now scoped to `erToK` (Tourlakis 0.1.0.44
⊇ direction) only.

### §3.1 Foundational tupling — bijection ℕ^{n+1} ≅ ℕ in ER and K^sim

K^sim's `simrec` is multi-output: the constructor produces a
vector of mutually-recursive functions. Translating it to ER
requires bridging multi-output K^sim morphisms to multi-
output ER morphisms without packing artefacts that defeated
prior attempts (the `3^E` coefficient that broke
`kToERDirect`).

**Note on choice of pairing function.** The literature
typically presents pairing constructions using Cantor's
`J(x,y) = (x+y)(x+y+1)/2 + y`. We use Szudzik (also called
"elegant") pairing: `Nat.pair x y = if x < y then y² + x
else x² + x + y` (mathlib's `Nat.pair`, exposed in our
project as `ERMor1.natPair`). Both are bijections
`ℕ × ℕ → ℕ` with the same polynomial value bound `≤
(max(x,y) + 1)²`; Szudzik's diagonal-versus-quadrant shape
gives a depth-ordering property convenient for inductive
arguments. Wherever the literature says "Cantor pairing",
our Lean realization uses Szudzik; the bound shape and
PolyBound-builder structure are identical.

We build fixed-length k-tuple Szudzik pairing as named
composites in ER, with the recursive shape:

- 1-tuple combining = identity.
- (n+2)-tuple combining = `pair` after `(proj 0,
  (n+1)-tuple combining of (proj 1, …, proj (n+1)))`.

(0-tuple combining is the unique morphism into the terminal
object; separately handled.)

This gives a categorical iso `(n+1) ≅ 1` in `LawvereERCat`
and `LawvereKSimDCat 2`, witnessed by the pack/unpack named
composites. By composition, `ERMor1 a ≅ ERMorN a (n+1)` in
the morphism quotient; same for K^sim.

The categorical iso is direct evidence that our free Lawvere
theory on ER does not have more computational content than
the standard non-categorical presentation: every multi-
output morphism is realized by a single-output one in the
quotient.

#### Lean entities

**Indexing convention.** Throughout Path 2, the parameter
`k : ℕ` of `tuplePack` / `tupleAt` indexes a tuple of
length `k + 1`. That is, `tuplePack k` packs a `(k+1)`-vector,
and `tupleAt k` extracts a component from a packed
`(k+1)`-vector. Empty (length 0) tuples are excluded by
construction: the bijection `(Fin (k+1) → ℕ) ↔ ℕ` is only
meaningful for non-empty products, and using `Fin (k+1)`
makes invalid (length-0) states unrepresentable rather than
requiring a `k ≥ 1` side condition.

Foundational layer (Lean Nat-level — `Utilities/Tupling.lean`):

- `Nat.tuplePack : (k : ℕ) → (Fin (k+1) → ℕ) → ℕ`. The
  parameter `k` packs a `(k+1)`-vector; `k = 0` is
  identity (1-tuple), `k+1` pairs the head with the packed
  remaining `(k+1)`-vector via Szudzik `Nat.pair`.
- `Nat.tupleAt : (k : ℕ) → ℕ → Fin (k+1) → ℕ`. Inverse:
  walk the right-fold-pair encoding.
- `Nat.tupleAt_tuplePack` and `Nat.tuplePack_tupleAt`:
  pack-unpack bijection theorems (`(Fin (k+1) → ℕ) ↔ ℕ`).
- `Nat.tuplePack_le`: polynomial value bound on packed
  tuple. The `Nat.pair x y ≤ (x + y + 1)^2` bound iterates
  through the recursion to give the closed form

  ```text
  tuplePack k v ≤ tuplePackCoef k * (M + 1)^(2^k)
  ```

  where `M = max v` over `Fin (k+1)` and
  `tuplePackCoef : ℕ → ℕ` is the computable Lean function

  ```text
  tuplePackCoef 0     = 1
  tuplePackCoef (k+1) = (tuplePackCoef k + 2)^2
  ```

  The bound is multiplicative-coefficient form
  `c_k · (M+1)^{2^k}` (matching `ERMor1.PolyBound`'s
  `coefficient * (max+1)^degree + constant` shape with
  `degree = 2^k`, `coefficient = tuplePackCoef k`,
  `constant = 0`).

  *Earlier drafts of this section stated the bound as
  `(M + c_k)^{2^k}` with a constant `c_k`; that formula is
  asymptotically correct but does not hold as a literal Lean
  inequality, since the leading coefficient of the iterated
  `pair`-bound (4 at the 2-tuple step) cannot be absorbed into
  the additive `c_k`. The multiplicative form
  `c_k · (M+1)^{2^k}` is the formally correct closed form and
  is what step 1 derives.*

ER layer (`Utilities/ERTupling.lean`):

- `ERMor1.tuplePack (k : ℕ) : ERMor1 (k+1)`. Interp =
  `Nat.tuplePack k`.
- `ERMor1.tupleAt (k : ℕ) (i : Fin (k+1)) : ERMor1 1`. Interp
  extracts component `i` from the packed value.
- `@[simp] ERMor1.interp_tuplePack`,
  `@[simp] ERMor1.interp_tupleAt`.
- `ERMor1.PolyBound.ofTuplePack`, `.ofTupleAt`. PolyBound
  builders certifying polynomial value bound.
- Round-trip lemmas at the interp level and at the
  ERMorN-quotient level.

K^sim layer (NOT BUILT under Path 2):

Pairing and projections at level ≤ 2 in K^sim do exist —
by Tourlakis 2018 §0.1.0.44 our `kToER` proves `K^sim_2 ⊆
ER`, and ER contains the pairing function and its
projections (per Tourlakis §0.1.0.34 proof, both J and its
projections K, L are in E^2). So K^sim_2 contains pairing
and unpair as functions, by the equivalence we are
proving. A naive K^sim construction (e.g. building Szudzik
unpair as `λz. μx ≤ z. ∃y ≤ z. J(x,y) = z`, a bounded
search whose body involves `λxy.xy ∈ K^sim_2`) hits level
3 by the obvious approach since K^sim_2 simrec children
must be at level ≤ 1 (Tourlakis §0.1.0.7) and `mul`-using
step-functions push the simrec to level 3. A less naive
construction at level ≤ 2 must exist (per the equivalence
we are proving) but is not yet on this project's roadmap.

Path 2 does not need K^sim-side tuplePack/tupleAt for the
load-bearing chain. The simrec case of `kToER` translates
each K^sim simrec into ER directly using
`ERMor1.simultaneousBoundedRec` (step 2), which only needs
ER-side tuplePack/tupleAt. K^sim's native multi-output
`simrec` constructor handles the K^sim side natively.

(K^sim-side tuplePack/tupleAt may turn out to be needed by
the erToK URM simulator at step 9; if so, it will be built
in that cycle. Constructing it then will require the
non-naive level-≤-2 approach — likely already published in
the literature on K^sim / loop-program hierarchies, though
we have not yet located the specific reference.)

Categorical packaging:

- `LawvereERCat.tupleIso (k : ℕ) : (k + 1) ≅ 1` in
  `LawvereERCat` (decorative, witnessing that ER-side
  products of the generator collapse via Szudzik pairing in
  the morphism quotient — a `(k+1)`-fold product is
  isomorphic to the generator). Useful for cleanly stating
  multi-output ER translations as single-output ones.
- The K^sim-side analogue is **not** built (see above).

Properties:

- ER-side pack and unpack carry polynomial value bounds
  (in the inputs); composing with k-tuple pack produces an
  ER expression whose value bound is polynomial of fixed
  degree depending on k (not on inputs).

### §3.2 Simultaneous bounded recursion in ER

ER's existing `ERMor1.boundedRec` (in
`Utilities/ERArith.lean` line 1782) is single-output: it
iterates a single step function with access to that
function's previous value only. K^sim's `simrec`
constructor is multi-output: each component's step has
access to all components' previous values. To translate
K^sim simrec into ER without packing artefacts, we build a
multi-output bounded-recursion named composite at the
`ERMorN` level whose implementation packs internally via
`Nat.tuplePack`.

#### Interface

```lean
def ERMor1.simultaneousBoundedRec
    (k : ℕ)                                        -- (k+1) components
    (a : ℕ)                                        -- input arity
    (h : Fin (k + 1) → ERMor1 a)                   -- bases
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))   -- steps
    (componentBound : ERMor1 (a + 1)) :            -- bound per component
    ERMorN (a + 1) (k + 1)
```

**Bound-input contract.** `componentBound` is a bound on
each individual component value at every iteration:
`f_j(n, x⃗) ≤ componentBound.interp (n, x⃗)` for all `j`.
The implementation derives the packed-state bound
internally (by composing with the §3.1 `tuplePack`
polynomial bound: packed state ≤
`tuplePackCoef k · (componentBound + 1)^{2^k}`), so
callers do NOT need to provide a packed-state bound. This
matches the §3.1 `Nat.tuplePack_le` formula and is what
the level-2 majorization in §3.4 supplies (the
`A_2^2(vMax v + offset)` bound is on each component, not
on the packed tuple).

Interpretation (when `componentBound` dominates each
component value at every iteration):

```text
(simultaneousBoundedRec k a h g componentBound) i (n, x⃗)
  = f_i(n, x⃗)
```

where `f_0, …, f_k` are simultaneously defined by:

- `f_j(0, x⃗) = h_j(x⃗)` (base case);
- `f_j(n+1, x⃗) = g_j(n, x⃗, f_0(n, x⃗), …, f_k(n, x⃗))`
  (step depends on all components).

#### Implementation outline (deferred to step 2's cycle)

1. Define a packed step function: unpack the previous
   packed state into (k+1) components via `tupleAt`,
   evaluate each `g_j` on the appropriate inputs, repack
   via `tuplePack`. Single-Nat-to-single-Nat function.
2. Derive the packed-state bound from `componentBound`
   using `Nat.tuplePack_le` (per §3.1's recurrence): if
   each `f_j(n, x⃗) ≤ componentBound.interp (n, x⃗)`, then
   `tuplePack k (f_0(n,x⃗), …, f_k(n,x⃗))` is bounded by
   `tuplePackCoef k * (componentBound.interp (n, x⃗) + 1)^{2^k}`
   (where the `tuplePack k` parameter packs a `(k+1)`-tuple
   per the §3.1 indexing convention). Express this packed-
   state bound in ER (closure under composition + iterated
   multiplication; stays in ER for any fixed `k`, with the
   bound's tower height at most `componentBound`'s tower
   height plus 1 by Module A's `tower_succ_pow_bound_strong`
   for `h ≥ 2`).
3. Apply `ERMor1.boundedRec` with the packed initial state
   `tuplePack k ∘ (h_0, …, h_k)`, the packed step, and
   the derived packed-state bound from step 2.
4. The `i`-th component of the output `ERMorN` is
   `tupleAt k i ∘ packed_state_at_recVar`.

The packing artefacts are encapsulated inside
`simultaneousBoundedRec`. Downstream `kToER` sees a clean
ERMorN multi-output interface with no `3^E` coefficient.

**Tower-height arithmetic.** If `componentBound` is at ER
tower height `h_c`, the packed-state bound (derived in step 2)
is at most height `max(h_c, 2) + 0` once `h_c ≥ 2` (per
`tower_succ_pow_bound_strong`'s height-fixed property), so
the whole `simultaneousBoundedRec` stays at the same tower
height as `componentBound`. For Path 2's level-2 case where
`componentBound = A_2^2(vMax v + offset)` (height 2), the
output stays at height 2.

#### Properties

- `simultaneousBoundedRec_interp_correct`: when `bound`
  dominates the iteration's component values pointwise, the
  ERMorN's interp matches the simultaneous recursion's
  semantic equations.
- `simultaneousBoundedRec_polyBound`: `PolyBound` for each
  component, derived from the bound's `PolyBound` and the
  packed-state arithmetic. Applies only when
  `componentBound` has a `PolyBound` — i.e. K^sim levels
  ≤ 1. At level 2 the chain instead uses
  `simultaneousBoundedRec_interp_correct` with a
  Nat-level dominance hypothesis from step 4 majorization;
  no `PolyBound` is produced for the level-2 simrec
  output.

K^sim has simultaneous recursion built-in (the `simrec`
constructor is the multi-output primitive); no
corresponding K^sim infrastructure is needed.

### §3.3 Tourlakis A_n named composites in ER

Following Tourlakis 2018 page 22 (proof of §0.1.0.44 ⊆):
A_1 = `λx. 2x + 2 ∈ ER`, A_2 = `λx. 2^x ∈ ER`. Iterated
versions A_n^r are r-fold composition of A_n with itself.

#### Lean entities (`Utilities/ERAMajorants.lean`)

- `ERMor1.A_one : ERMor1 1`. Interp `λx. 2*x + 2`.
  Construction via existing named composites: e.g.
  `ERMor1.comp ERMor1.addN
    (![ERMor1.comp ERMor1.succ (ERMor1.proj 0),
       ERMor1.comp ERMor1.succ (ERMor1.proj 0)])`
  or any equivalent.
- `ERMor1.A_one_iter : ℕ → ERMor1 1`. r-fold composition of
  `A_one` with itself. Interp `λx. 2^r · x + (2^{r+1} − 2)`.
- `ERMor1.A_two_iter (r : ℕ) := ERMor1.towerER r`
  (existing — see `def ERMor1.towerER` in
  `LawvereERBoundComputable.lean`).  Interp
  `tower r x` = `A_2^r(x)`.  No separate unary
  `ERMor1.A_two : ERMor1 1` definition: Tourlakis's
  `A_2 = λx. 2^x` is exactly `A_two_iter 1` (since
  `tower 1 x = 2^x` per `Utilities/Tower.lean`), and
  introducing a third name for the same expression
  invites confusion.  (`ERMor1.expER : ERMor1 2`
  computes the binary `λ(n, y). y^n`, not the unary
  `λx. 2^x`; partial application would be needed to
  recover the unary form, which is why aliasing
  `A_two = expER` is type-inconsistent.)

#### Polynomial bound certification

- `ERMor1.PolyBound.ofA_one`: PolyBound for `A_one`
  (linear-shape; degree 1).
- `ERMor1.PolyBound.ofA_one_iter`: PolyBound for
  `A_one_iter r` (degree 1, coefficient `2^r`,
  constant `2^{r+1} − 2`).
- No PolyBound for `A_two_iter`. `tower r x` for `r ≥ 1`
  is not polynomially bounded in `x`, and
  `ERMor1.PolyBound`'s structural-towerHeight section
  (`LawvereERPolynomialBound.lean`) explicitly restricts
  the per-constructor builder set to the bprod-free
  fragment; `expER` (and therefore `towerER` and
  `A_two_iter`) is bprod-based and falls outside that
  fragment.  The level-2 chain consumes the
  Nat-level inequality
  `f.interp v ≤ (A_two_iter r).interp ![vMax v]`
  produced by step 4 majorization, fed into
  `simultaneousBoundedRec_interp_correct`'s dominance
  hypothesis.  Step 5's kToER simrec at level 2 uses the
  ER term `simultaneousBoundedRec` (the term-builder)
  with this `componentBound`, never invoking
  `ofSimultaneousBoundedRec` (the PolyBound builder).

### §3.4 Majorization theorem (Tourlakis 0.1.0.10 transcribed)

For every `f : KMor1 a` with `f.level ≤ n` (where n ≤ 2),
there is a Lean-computable `r` such that:

```text
∀ v : Fin a → ℕ, f.interp v ≤ (A_n_iter r).interp (vMax v)
```

The `r` is a Lean function of f's structure; the
existential is constructive.

#### Proof structure (structural induction)

- **Level-0 atoms** (`zero`, `succ`, `proj`): bounded by a
  `linearBound` with small constants per existing
  `KMor1.linearBound_dominates_level_zero`. Translated to
  `A_1^r` via `linearBound_le_A_one_iter` (below).
- **Level-1** (comp + simrec with K^sim_0 children +
  raise): bounded by `KMor1.linearBound` (linear-shape
  bound) per existing `KMor1.linearBound_dominates_level_one`
  in `LawvereKSimPolynomialBound.lean`. Translated via
  `linearBound_le_A_one_iter`.
- **Level-2** (comp + simrec with K^sim_1 children +
  raise): each component's step function is at K^sim_1,
  bounded by `A_1^{r_1}`. Iterating
  `simultaneousBoundedRec` `n` times accumulates per-step
  bounds; the result at iteration `n` is bounded by
  `A_2^{r_2}` for an explicit `r_2 = O(r_1 + log n)`. This
  is the substantive new content; it uses the
  `simultaneousBoundedRec` interface (so no packing-coefficient
  artefacts).

#### `linearBound_le_A_one_iter` translation

```lean
theorem linearBound_le_A_one_iter (c d : ℕ) :
  let r := max ⌈log_2 (c + 1)⌉ (⌈log_2 (d + 2)⌉)
  ∀ x, c * x + d ≤ (ERMor1.A_one_iter r).interp ![x]
```

We need `A_1^r(x) = 2^r · x + (2^{r+1} − 2) ≥ c · x + d`,
i.e. `2^r ≥ c` and `2^{r+1} − 2 ≥ d`, i.e. `2^{r+1} ≥ d + 2`.

- `2^r ≥ c` ⇐ `r ≥ ⌈log_2 (c + 1)⌉` (with `c = 0` trivial).
- `2^{r+1} ≥ d + 2` ⇐ `r + 1 ≥ ⌈log_2 (d + 2)⌉`, i.e.
  `r ≥ ⌈log_2 (d + 2)⌉ − 1`. Conservatively take
  `r ≥ ⌈log_2 (d + 2)⌉` (one bit of slack; correct at all
  edge cases including `d = 0, 1, 2`).

Edge cases:

- `d = 0`: `⌈log_2 2⌉ = 1`, `r ≥ 1` gives `A_1^1(x) = 2x + 2
  ≥ c·x` for `c ≤ 2`. For `c > 2` the c-bound dominates.
- `d = 1`: `⌈log_2 3⌉ = 2`, `r ≥ 2` gives `A_1^2(x) = 4x + 6
  ≥ c·x + 1`. ✓
- `c = 0, d = 0`: the formula gives `r = max 0 1 = 1`
  (`A_1^1(x) = 2x + 2 ≥ 0`); `r = 0` would also be valid
  (`A_1^0(x) = x ≥ 0`) but the formula picks `r = 1`.
- `c = 0`: `⌈log_2 1⌉ = 0`, so `r = ⌈log_2 (d + 2)⌉ ≥ 1`
  for `d ≥ 0`. ✓

Lean proof + `#guard` tests at `(c, d) ∈ {(0,0), (0,1),
(1,0), (1,1), (2,0), (2,5)}` confirm correctness. Step 4's
cycle finalizes the formula.

#### Lean theorem statement (constructive `r`)

Per the constructive discipline, the bound's `r` is split
into an explicit `def` and a separate `theorem`:

```lean
def KMor1.majorize_r {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) : ℕ :=
  -- bottom-up structural recursion on f
  ...

theorem KMor1.majorize_by_A_two_iter
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) (v : Fin a → ℕ) :
  f.interp v ≤
    (ERMor1.A_two_iter (KMor1.majorize_r f h)).interp ![vMax v]
```

(With a tighter version for `f.level ≤ 1` using A_1: split
into `KMor1.majorize_r_one` and
`KMor1.majorize_by_A_one_iter`.)

`r` is a Lean function of `f`'s structure; no
`Classical.choose` consumer downstream. (`LawvereKSimMajorization.lean`.)

#### Prose proof of the level-2 case (the load-bearing math)

This is the key arithmetic that distinguishes Path 2 from
the failed v2-v5 attempts. The level-0 and level-1 cases
reduce to existing `KMor1.linearBound_dominates` plus
`linearBound_le_A_one_iter`. The level-2 case is genuinely
new content.

**Setup.** Consider `f : KMor1 a` with `f.level ≤ 2`. The
non-trivial sub-cases are `simrec` (since `comp` and
`raise` are passthrough at the bound level — see below).
For a level-2 `simrec`, we have:

- `f = simrec (i : Fin (k+1)) (h : Fin (k+1) → KMor1 a) (g
  : Fin (k+1) → KMor1 (a+1+(k+1)))` with all `h_j` and
  `g_j` at K^sim level ≤ 1.
- `f.interp` over `(n, x⃗) : Fin (a+1) → ℕ`: defined by
  simultaneous primitive recursion. Let `F_j(n, x⃗) :=`
  the `j`-th simrec component evaluated at `(n, x⃗)`.

**Inductive hypothesis.** For each child `h_j` and `g_j`,
the level-1 majorization gives explicit `r_h, r_g : ℕ`
such that:

- `(h_j).interp x⃗ ≤ A_1^{r_h}(max x⃗)`.
- `(g_j).interp (n, x⃗, F_0, ..., F_k) ≤ A_1^{r_g}(max(n,
  max x⃗, F_0, ..., F_k))`.

By taking the max over `j ∈ Fin (k+1)`, set:

- `r_H := max_j r_{h,j}` so each `(h_j).interp x⃗ ≤
  A_1^{r_H}(max x⃗)`.
- `r_G := max_j r_{g,j}` so each `(g_j).interp ... ≤
  A_1^{r_G}(max(n, max x⃗, F_0, ..., F_k))`.

**Iteration arithmetic.** Let `M_n := max_j F_j(n, x⃗)`.
The recursion equations give:

- `M_0 = max_j (h_j).interp x⃗ ≤ A_1^{r_H}(max x⃗)`.
- `M_{n+1} = max_j (g_j).interp (n, x⃗, F_0(n,x⃗), ...,
  F_k(n,x⃗)) ≤ A_1^{r_G}(max(n, max x⃗, M_n))`.

For `n ≥ max x⃗` (the only regime that matters; smaller
inputs give smaller bounds), we have `max(n, max x⃗) = n`,
so `M_{n+1} ≤ A_1^{r_G}(max(n, M_n))`.

**Closed-form bound on M_n.** We show by induction on `n`:

```text
M_n ≤ A_1^{r_H + n · r_G}(max(n, max x⃗))
```

- **Base (n = 0)**: `M_0 ≤ A_1^{r_H}(max x⃗) ≤
  A_1^{r_H}(max(0, max x⃗))`. ✓
- **Step (n → n+1)**: by IH, `M_n ≤ A_1^{r_H + n·r_G}(max(n,
  max x⃗))`. Since `A_1` is monotone (and `A_1^k` is
  monotone), and `max(n, max x⃗) ≤ max(n+1, max x⃗)`:

```text
M_{n+1} ≤ A_1^{r_G}(max(n, M_n))
       ≤ A_1^{r_G}(max(n, A_1^{r_H + n·r_G}(max(n, max x⃗))))
       ≤ A_1^{r_G}(A_1^{r_H + n·r_G}(max(n, max x⃗)))
       = A_1^{r_H + (n+1)·r_G}(max(n, max x⃗))
       ≤ A_1^{r_H + (n+1)·r_G}(max(n+1, max x⃗))
```

(The third step uses `n ≤ A_1^{r_H + n·r_G}(max(n, max
x⃗))` — true since `A_1^k(y) ≥ y` for any `k ≥ 0` —
followed by `A_1` being monotone.) ✓

**Bounding A_1^{linear_in_n} by A_2^constant.** We have
`M_n ≤ A_1^{r_H + n·r_G}(max(n, max x⃗))`. The exponent
`r_H + n·r_G` is linear in `n`; the input `max(n, max x⃗)`
is linear in `n` and inputs. Use the closed-form
`A_1^k(x) = 2^k · x + (2^{k+1} − 2)`:

```text
A_1^{r_H + n·r_G}(M)
  = 2^{r_H + n·r_G} · M + 2^{r_H + n·r_G + 1} − 2
  ≤ 2^{r_H + n·r_G + 1} · (M + 1)
```

For `M = max(n, max x⃗)` and `n ≤ max(n, max x⃗)`, we
have:

```text
A_1^{r_H + n·r_G}(max(n, max x⃗))
  ≤ 2^{r_H + (max(n, max x⃗))·r_G + 1} · (max(n, max x⃗) + 1)
  ≤ 2^{(r_H + r_G + 2) · (max(n, max x⃗) + 1)}
  ≤ 2^{2^{(max(n, max x⃗) + r_H + r_G + 2)}}
  = A_2^2(max(n, max x⃗) + r_H + r_G + 2)
```

(The third step uses `(r_H + r_G + 2) · (m + 1) ≤
2^{m + r_H + r_G + 2}` for `m = max(n, max x⃗)`, which
holds for `m + r_H + r_G + 2 ≥ 4` — i.e. always for
non-trivial cases — by `k · (m+1) ≤ 2^{m + log_2 k +
small}` plus monotonicity of `2^x`.)

**Substituting `n ≤ max v 0 = vMax v`.** The simrec's
recursion variable is `v 0` (component 0 of the input
vector), bounded by `vMax v`. So at the top:

```text
F_i(v 0, x⃗) = M_{v 0}_, i ≤ M_{v 0}
            ≤ A_2^2(max(v 0, max x⃗) + r_H + r_G + 2)
            ≤ A_2^2(vMax v + r_H + r_G + 2)
```

**Conclusion.** Set:

```text
r_2 := 2
offset_2 := r_H + r_G + 2
```

Then `f.interp v = F_i(v 0, x⃗) ≤ A_2^{r_2}(vMax v +
offset_2)`. The bound is at fixed tower height 2, with an
explicit additive offset depending only on the children's
majorant constants `r_H, r_G` (themselves Lean-`Nat`
functions of `f`'s structure).

**Recursive comp / raise cases.** For `comp f gs` and
`raise f`: the bound is built bottom-up from children's
bounds, with the height staying at 2 (or below) by Module
A's `tower_succ_pow_bound_strong` (height-fixed for
`h ≥ 2`). Concrete formulas: step 4's cycle.

**Why this avoids the prior trap.** The key arithmetic is
`A_1^{linear} ≤ A_2^{constant}`, NOT `polynomial-of-tower
≤ tower`. The factor `r_H + r_G + 2` is additive in the
offset, not multiplicative coefficient on the input. There
is no `3^E` or `c^k` blowup; the bound's tower height
stays at fixed 2 across all level-2 K^sim morphisms, and
the offset accumulates additively. This is the
mathematical reason Path 2 succeeds where the prior
strategies failed: the iteration arithmetic over `A_1^k`
(linear) telescopes cleanly into a single `A_2^2`
application, whereas the prior `kSimTowerBound` shape
inserted an extra `Nat.log 2 (3^E)` factor that couldn't
absorb into linear-in-stepTH.

**Adversarial-review obligation for step 4's cycle.** This
prose proof must be Lean-realized as
`KMor1.majorize_by_A_two_iter` with explicit `r_2 = 2` and
`offset_2 = r_H + r_G + 2`. Step 4's adversarial review
must verify the iteration arithmetic step-by-step in Lean
and check that the boundary cases (`n = 0`, `max x⃗ = 0`)
go through.

### §3.5 `kToER` by structural induction

```lean
def kToER : ∀ {a : ℕ} (f : KMor1 a), f.level ≤ 2 → ERMor1 a
  | _, .zero,                _ => ERMor1.zeroN _
  | _, .succ,                _ => ERMor1.succ
  | _, .proj i,              _ => ERMor1.proj i
  | _, .comp f gs,           h =>
      ERMor1.comp (kToER f h_f)
                  (fun i => kToER (gs i) (h_gs i))
  | _, .simrec i h₀ gs,      h =>
      let bases : Fin (k + 1) → ERMor1 a :=
        fun j => kToER (h₀ j) (h_h₀ j)
      let steps : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
        fun j => kToER (gs j) (h_gs j)
      let r := KMor1.majorize_r f h
      let bound : ERMor1 (a + 1) :=
        ERMor1.comp (ERMor1.A_two_iter r)
                    ![ERMor1.sumCtxER (a + 1)]
                    -- `sumCtxER` dominates `maxCtx`
                    -- pointwise; using it gives a slightly
                    -- looser but valid bound. Step 5's
                    -- cycle may build a tighter
                    -- `ERMor1.maxCtxER` named composite if
                    -- desired.
      ERMor1.simultaneousBoundedRec k a bases steps bound i
  | _, .raise f,             h => kToER f h_f
```

(Indexing details elided; concrete signature at step 5's
cycle.)

Each constructor case is a one-line `match` invoking either
a named composite or `simultaneousBoundedRec` with the
A_n^r bound. No URM, no packing at the kToER level (packing
happens internally inside `simultaneousBoundedRec`), no
`linearBound`-only argument at level 2 (the bound is
explicitly A_n^r per Tourlakis).

#### Interpretation-preservation

```lean
theorem kToER_interp
    {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2) (v : Fin a → ℕ) :
  (kToER f h).interp v = f.interp v
```

Proof by structural induction on `f`:

- Atoms: by definitional unfolding of named composite
  interps.
- `comp`: by unfolding `ERMor1.comp.interp` plus inductive
  hypothesis.
- `simrec`: by `simultaneousBoundedRec_interp_correct`
  applied to bases and steps from the inductive hypothesis,
  plus the majorization theorem (so `bound` dominates the
  iteration values, ensuring `boundedRec`'s truncation does
  not fire).
- `raise`: passthrough.

Mirror `kToERN_interp` for multi-output K^sim morphisms.

#### Functor lift

```lean
def kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat where
  obj n := n
  map ⟦f, h⟧ := ⟦kToER f h⟧
  map_id := by ...      -- via kToER_interp
  map_comp := by ...    -- via kToER_interp
```

Functor laws fall out of `kToER_interp` and the morphism-
quotient setup (extensional equality of interps gives class
equality).

### §3.6 Tourlakis result-to-Lean-entity catalogue

- **§0.1.0.4 (A_n def)** — `ERMor1.A_one` (build, §3.3);
  `A_2 = λx. 2^x` realized as `A_two_iter 1`
  (= `towerER 1`); no separate unary `A_two` named
  composite (see §3.3 Lean entities subsection).
- **§0.1.0.5 (K_n majorization)** — (not directly used; the
  K^sim version is 0.1.0.10).
- **§0.1.0.7 (K^sim def)** — `KMor1` inductive
  (`LawvereKSim.lean`). Existing ✓.
- **§0.1.0.8 (K_n ⊆ K^sim_n)** — (not directly used).
- **§0.1.0.9 (A_n ∈ K^sim_n)** — (not directly used by
  kToER).
- **§0.1.0.10 (K^sim_n majorization by A_n^k)** —
  `KMor1.majorize_by_A_n_iter`. Build, §3.4, step 4.
- **§0.1.0.15 (K^sim_n = L_n)** — (not directly used).
- **§0.1.0.17 (a) (`λxy.x+y` ∈ K^sim_1)** — `ERMor1.addN`.
  Existing ✓.
- **§0.1.0.17 (b) (`λxy.xy` ∈ K^sim_2)** — `ERMor1.mulN`.
  Existing ✓.
- **§0.1.0.17 (c) (`λx.2^x` ∈ K^sim_2)** — realized by
  `A_two_iter 1` = `ERMor1.towerER 1` (since
  `tower 1 x = 2 ^ x` per `Utilities/Tower.lean`).  No
  separate unary `ERMor1.A_two` exists; `ERMor1.expER :
  ERMor1 2` realizes the binary `λ(n, y). y ^ n`, not
  the unary form (see §3.3 Lean entities).
- **§0.1.0.22 (Grzegorczyk hierarchy def)** — NOT
  formalized. Excluded by §1.4.
- **§0.1.0.27 (bounding lemma for E^n)** — not used; we use
  Module A's tower lemmas directly.
- **§0.1.0.30 (E^n closed under bounded summation)** —
  `ERMor1.bsum` (ER primitive constructor). Existing ✓.
- **§0.1.0.32 (E^n closed under bounded search)** —
  `ERMor1.boundedSearch`. Existing ✓.
- **§0.1.0.34 (E^2 closed under bounded recursion)** —
  `ERMor1.boundedRec`. Existing ✓.
- **§0.1.0.35 (E^{n+1} closed under simultaneous bounded
  recursion)** — `ERMor1.simultaneousBoundedRec`. Build,
  §3.2, step 2.
- **§0.1.0.34 (proof, p. 13) and §0.1.0.17 (b)** —
  Tourlakis's witness for pairing in E^2 is Cantor's
  `J = λxy. (x+y)^2 + x` (mul ∈ K^sim_2 per §0.1.0.17 (b)
  and `λxy. x+y` ∈ K^sim_1 per §0.1.0.17 (a) compose to
  give Cantor's `J` in E^2). Our Lean formalization uses
  Szudzik pairing instead (see the note in §3.1); the
  reasoning that pairing is in E^2 is identical, since
  Szudzik's defining expression is also a polynomial in
  `mul` and `add`. Lean: `ERMor1.natPair`,
  `natUnpairFst`, `natUnpairSnd`.
  Existing ✓. (Note: the design originally cited §0.1.0.39
  here; that section is in fact about the URM-simulating
  functions in K_4 and is not what we want.)
- **§0.1.0.43 (Ritchie–Cobham property of E^n)** — used
  for `erToK` only, via §4–§9 URM material. Not directly
  realized as a Lean theorem.
- **§0.1.0.44 (K^sim_n = E^{n+1})** — `kToER_interp` (⊆
  direction, step 5) and `erToK_interp` (⊇ direction, step
  10). The categorical iso (step 11) packages these.
- **Tourlakis CN §4.2.2 (Hilbert-Bernays sequence
  coding)** — `ERMor1.beta`. Existing ✓.
- **Tourlakis CN §10.2.20 (cross-ref)** — not directly
  used.

#### Existing landed infrastructure (verified)

- `ERMor1.boundedRec` at `Utilities/ERArith.lean:1782`.
- `ERMor1.expER` at `LawvereERArith.lean:25`.
- `ERMor1.towerER` at `LawvereERBoundComputable.lean:230`.
- `ERMor1.addN`, `mulN`, `natN`, `signN`, `ltN`, `leN`,
  `condN`, `pred`, `minN`, `natPair`, `natUnpairFst`,
  `natUnpairSnd`, `beta`, `boundedSearch`, `sumCtxER` —
  all in `Utilities/ERArith.lean`.
- `ERMor1.PolyBound` infrastructure with builders for each
  ER constructor, in `LawvereERPolynomialBound.lean`.
- `tower` Lean function in `Utilities/Tower.lean` plus
  monotonicity lemmas.
- `polynomial_iter_tower_bound`,
  `tower_succ_pow_bound_strong` in
  `Utilities/ComputationalComplexity.lean`.
- `Nat.seqPack`, `Nat.seqAt` in `Utilities/SzudzikSeq.lean`
  (for variable-length sequences; we add k-tuple pairing
  per §3.1).
- `KMor1.linearBound`, level-0 + level-1 dominance theorems
  in `LawvereKSimPolynomialBound.lean`. These are reused
  via `linearBound_le_A_one_iter` to obtain A_1^r dominance
  at levels 0 and 1.

### §3.7 Module file layout for Path 2 kToER

(In addition to the URM-related modules in §12 for the
erToK side.)

```text
GebLean/Utilities/Tupling.lean                       [step 1]
  Nat.tuplePack, Nat.tupleAt, bijection theorems,
  polynomial value bound.

GebLean/Utilities/ERTupling.lean                     [step 1]
  ERMor1.tuplePack, ERMor1.tupleAt, PolyBound builders,
  interp lemmas; LawvereERCat.tupleIso.

(K^sim-side tupling NOT BUILT under Path 2; see §3.1.)

GebLean/Utilities/ERSimultaneousBoundedRec.lean      [step 2]
  ERMor1.simultaneousBoundedRec (multi-output);
  packs internally via tuplePack, recurses via boundedRec,
  unpacks via tupleAt.

GebLean/Utilities/ERAMajorants.lean                   [step 3]
  ERMor1.A_one, A_one_iter; A_two_iter alias; PolyBound
  builders for the A_one variants only (A_two_iter is
  tower-fast; no PolyBound).

GebLean/LawvereKSimMajorization.lean                 [step 4]
  KMor1.majorize_by_A_n_iter (Tourlakis 0.1.0.10);
  linearBound_le_A_one_iter translation.

GebLean/LawvereKSimER.lean                           [step 5]
  kToER, kToER_interp, kToERN, kToERN_interp,
  kToERFunctor, functor laws.
```

### §3.8 Why this avoids the prior `kToERDirect` failure

The `kToERDirect` attempts (v2-v5 + prose) failed at level
2 due to specific Lean-side artefacts of the bound shape we
chose:

- `kSimPackedStep_polyBound`'s `coefficient = 3^E` field
  arose from Szudzik packing combined with our specific
  bound-tracking structure in
  `LawvereKSimPolynomialBound.lean`.
- The level-2 absorption inequality `log_2(C+1) ≤ stepTH +
  small` failed because LHS grew as `4^k` while RHS only
  linear in `k`.

Path 2 avoids these by:

- Using k-tuple Szudzik pairing (§3.1) packaged as named
  composites with proven polynomial value bounds.
- Encapsulating all packing inside `simultaneousBoundedRec`
  (§3.2). Callers (the kToER structural induction) see a
  clean ERMorN multi-output interface; the packing
  arithmetic does not leak into majorization or interp-
  preservation proofs.
- Using Tourlakis's exact `A_n^r` bound shape (§3.3, §3.4)
  rather than our own `kSimTowerBound` shape. The Tourlakis
  bound has known clean closure properties documented in
  the literature.
- Preserving existing level-0 and level-1 dominance
  theorems via `linearBound_le_A_one_iter` translation,
  rather than re-proving those levels from scratch with a
  new bound shape.

The level-2 majorization proof (the only fresh dominance
work needed) operates on
`simultaneousBoundedRec`'s clean ERMorN interface and the
A_n^r bound shape, not on the prior `kSimTowerBound` shape
that defeated us.

---

## §4 URM definition

### §4.1 Primitives

Tourlakis 2018 §0.1.0.43 proof, PR-complexity-topics.pdf p. 19,
exhibits URMs with the following six instruction types
(transliterated from Tourlakis's notation):

```lean
inductive URMInstr (r : ℕ) : Type
  | zeroReg   (i : Fin r)              : URMInstr r
  | incReg    (i : Fin r)              : URMInstr r
  | decReg    (i : Fin r)              : URMInstr r
  | condJump  (i : Fin r) (t : ℕ)      : URMInstr r
  | gotoInstr (t : ℕ)                  : URMInstr r
  | stop                               : URMInstr r
```

Semantics on PC and register vector:

| Instruction | PC update | Register update |
| - | - | - |
| `zeroReg i` | `pc + 1` | `regs[i] := 0` |
| `incReg i` | `pc + 1` | `regs[i] := regs[i] + 1` |
| `decReg i` | `pc + 1` | `regs[i] := regs[i] ∸ 1` (truncated) |
| `condJump i t` | `t` if `regs[i] = 0`, else `pc + 1` | unchanged |
| `gotoInstr t` | `t` | unchanged |
| `stop` | `pc` (self-loop) | unchanged |

**Note on `condJump` shape.** Tourlakis's literal notation is
two-target: `if V_i = 0 goto m else goto m'`. Our `condJump i
t` is one-target: jump to `t` on zero, fall through to `pc + 1`
otherwise. Tourlakis's two-target form is recovered by a named
composite `condJumpTwoTarget i t1 t2 := condJump i t1;
gotoInstr t2`, which is the first entry of the helper-named-
composite catalogue. Expressively identical; the simplification
reduces the simulator's per-instruction case arity by one
branch.

### §4.2 `URMProgram`

```lean
structure URMProgram where
  numRegs : ℕ
  instrs : List (URMInstr numRegs)
  outputReg : Fin numRegs
```

A program is a finite list of instructions over a fixed register
arity, plus a designated output register. The PC ranges over
`{0, …, instrs.length}`; PC = `instrs.length` is the implicit
halt state (no instruction at that index, transition self-loops).

### §4.3 Link to abstract `RegisterMachine`

```lean
def URMProgram.toRegisterMachine (P : URMProgram) :
    RegisterMachineNS.RegisterMachine where
  numStates := P.instrs.length + 1
  numRegs := P.numRegs
  startState := 0
  transition := fun pc regs =>
    match P.instrs[pc.val]? with
    | none => (pc, regs)                          -- halt fixpoint
    | some instr => instrSemantics instr pc regs
```

`instrSemantics` dispatches on the instruction and returns
`(new_pc, new_regs)` per the table in §4.1. Out-of-range PC is a
self-loop. The existing `step`, `run`, `runFromConfig`, `runReg`
operations in `RegisterMachine.lean` apply to
`P.toRegisterMachine` immediately.

### §4.4 `URMComputes` — correctness with bound

```lean
structure URMComputes
    (P : URMProgram)
    (n : ℕ)
    (initRegs : Fin n → Fin P.numRegs)
    (outReg : Fin P.numRegs)
    (f : (Fin n → ℕ) → ℕ) where
  stepBound : (Fin n → ℕ) → ℕ
  correct :
    ∀ v t, stepBound v ≤ t →
    runReg P.toRegisterMachine
           (initialRegsFrom v initRegs) t outReg = f v
  towerHeight : ℕ
  towerOffset : ℕ
  towerDominates :
    ∀ v, stepBound v ≤ tower towerHeight (vMax v + towerOffset)
```

Where `initialRegsFrom v initRegs : Fin P.numRegs → ℕ` places `v`
at the indices listed by `initRegs` and 0 elsewhere; `vMax v` is
`Fin.foldr max 0 v` (zero on empty input).

`initRegs` is required to be injective: the URM's input
register-slots are distinct. The compiler ensures this by
allocating fresh register indices for each input. The
injectivity hypothesis is carried as a separate field of
`URMComputes` (or as a precondition on the structure's
constructor); concrete encoding to be settled at step 2.

The fields' meanings:

- `stepBound` — Lean `Nat`-valued function expressing the URM's
  exact step count as ordinary arithmetic on the input vector.
  Composes naturally under sequential / conditional / loop
  combinators (§5).
- `correct` — once at least `stepBound v` steps have elapsed, the
  output register holds `f v`. Uses `≤ t`, not `= stepBound`,
  because the `stop` self-loop guarantees stability past the
  bound (running longer does no harm).
- `towerHeight, towerOffset` — Lean `Nat` constants per
  subroutine, fixed once and for all. Together they witness the
  literature-aligned tower bound on `stepBound`.
- `towerDominates` — the closing inequality, a per-subroutine
  obligation. The shape `tower h (vMax v + offset)` lines up with
  Tourlakis 2018 §0.1.0.27 clauses (1)-(4) and Cutland Theorem
  4.1.1.

The structure is constructive: no field uses `∃`, all
witnesses are explicit Lean functions or constants. Step-0 design
is to keep the structure unconditionally constructive in line with
CLAUDE.md.

### §4.5 Lifting to `ElementaryBound`

`RegisterMachine.lean`'s `ElementaryBound` (lines 102-145, unary
shape) is recovered from `URMComputes`:

```lean
def URMComputes.toElementaryBound
    (uc : URMComputes P n initRegs outReg f) (v : Fin n → ℕ) :
    ElementaryBound where
  f := fun _ => uc.stepBound v
  height := uc.towerHeight
  offset := uc.towerOffset + vMax v
  dominated := fun _ => /- proof from `uc.towerDominates v` plus
                         arithmetic on the `vMax v` shift; concrete
                         proof in step 2 -/
                        _
```

Existing downstream uses of `ElementaryBound` in
`LawvereTreeERArith.lean` are unaffected.

---

## §5 Composition combinators in URM

Each combinator takes one or more `URMComputes` instances and
produces a `URMComputes` instance for the combined program. The
`stepBound` arithmetic is concrete Lean `Nat` arithmetic
(sum / max / iterated sum). The tower-witness arithmetic is
derived from existing Module A lemmas
(`Utilities/ComputationalComplexity.lean`); the design names
the lemmas to apply but defers the precise `(towerHeight,
towerOffset)` formulas to step 2's cycle.

### §5.1 Sequential composition `urmSeq`

`urmSeq P Q rmap : URMProgram`: run `P` first, then `Q` with
`Q`'s registers remapped via `rmap` (so `Q` sees `P`'s output
registers as its inputs). Defined by appending instruction
lists with PC-shift on `Q`'s `condJump` and `gotoInstr` targets.

`URMComputes` arithmetic:

- `stepBound (P;Q) v = stepBound P v + stepBound Q v'`
  where `v'` is `Q`'s input wired from `P`'s output on `v`.
- Tower witness derived using `tower_succ_pow_bound` (or
  `tower_succ_pow_bound_strong` for the `h ≥ 2` case) from
  `Utilities/ComputationalComplexity.lean`. Concrete formula:
  step 2's cycle. Sum-of-two-tower-bounded functions stays at
  the same height with a linear offset shift when both heights
  are ≥ 1, and bumps height by 1 when starting from height 0.

### §5.2 Conditional composition `urmIf`

`urmIf cond P Q : URMProgram`: at instruction 0, test `cond` (a
register expression); branch to either `P` or `Q`'s prelude.
Defined via `condJump` on the test register.

`URMComputes` arithmetic:

- `stepBound (urmIf c P Q) v
   = max(stepBound P v, stepBound Q v) + O(1)`.
- Tower witness: `towerHeight = max(towerHeight P, towerHeight
  Q)`; offset increases by a small constant. No height jump
  (max at same level absorbs `O(1)` additive overhead).

### §5.3 Bounded loop `urmLoop`

`urmLoop counter body : URMProgram`: execute `body` exactly
`regs[counter]` many times. Defined via the standard pattern
(Tourlakis 2018 p. 20):

```text
B ← counter
goto L
M:
  body
  B ← B ∸ 1
L: condJump B (L+1)
   gotoInstr M
L+1:
```

`URMComputes` arithmetic:

- `stepBound (urmLoop c P) v
   = sum_{i < c_v} stepBound_P (state_i) + O(c_v)`
  where `c_v` is `regs[c]` as a function of `v` and `state_i`
  is the register vector at iteration `i`.
- Tower witness derived using `polynomial_iter_tower_bound`
  from `Utilities/ComputationalComplexity.lean`, which states:
  iterating a polynomially-bounded step over a linearly-bounded
  initial value `j` times stays bounded by `tower 2 (linear of
  inputs)`. Concrete formula: step 2's cycle. The
  height-jump-per-loop-nesting matches the level grading of
  Tourlakis's hierarchy: each simrec / loop layer contributes
  at most one step in the tower, and the K^sim_2 case (two
  nested loops over polynomial bodies) lands in `tower 2`.

### §5.4 Composition arithmetic summary

For the load-bearing case (K^sim_2 → URM compilation), the
goal of the §5 arithmetic is for the URM compiled from any
K^sim morphism of level ≤ 2 to land in `tower 2` for its
`stepBound`. The bound `tower 2 (linear)` is in ER directly
(via iterated `2^x`-style ER expressions; see §1.4 and §9.2).
The shape mirrors the bound shape that Tourlakis 2018
§0.1.0.27 (4) and §0.1.0.43-44 use for `E^3`-runtimes (the
`A_2`-tower bound), but the construction in our project lives
entirely in `ERMor1` and does not invoke the ER ↔ E^3
equivalence. Step 2's cycle proves that the combinator
arithmetic carries the bound through.

---

## §6 The two catalogues (erToK side)

Under Path 2, the URM material is needed only for the
`erToK` direction (which compiles ER → URM, then simulates
URM in K^sim). Two catalogues are needed:

- §6.1 `URMSubroutinesER.lean` — URM subroutines emulating
  each ERMor1 constructor; used by the ER → URM compiler.
- §6.2 `KSimSubroutinesURM.lean` — K^sim subroutines
  emulating each URM primitive; used by the URM → K^sim
  simulator.

The earlier Path-1 design also catalogued URM subroutines
emulating K^sim atoms (used by a K^sim → URM compiler) and
ER subroutines emulating URM primitives (used by a URM → ER
simulator). Path 2 does not use either compiler or simulator
direction (kToER goes K^sim → ER directly via structural
induction in §3), so those two catalogues are not built.

Each catalogue is a Lean module exporting a list of named
program / term entries, each with its `URMComputes` (or
`KSimSimulatorRealizes`) lemma. The compiler and simulator
are then literal `match` expressions referencing catalogue
entries.

### §6.1 `URMSubroutinesER.lean` — URM realizations of ER atoms

Used by the ER → URM compiler (step 8).

| ER constructor | URM subroutine | `stepBound` | `tH` |
| - | - | - | - |
| `ERMor1.zero` | `urmSubrZero` | `1` | `0` |
| `ERMor1.succ` | `urmSubrSucc` | `1` | `0` |
| `ERMor1.proj i` | `urmSubrProj i` | `v[i] + 1` (copy) | `0` |
| `ERMor1.sub` | `urmSubrSub` | `v[1] + 1` (dec loop) | `0` |
| `ERMor1.comp f gs` | `urmSubrComp` (comb.) | sum over subs | per §5.1 |
| `ERMor1.bsum f` | `urmSubrBsum` (comb.) | iter sum | per §5.3 |
| `ERMor1.bprod f` | `urmSubrBprod` (comb.) | iter sum + mult | per §5.3 |

(`tH` abbreviates `towerHeight`. Combinator entries delegate
their tower-height arithmetic to the corresponding §5
combinator; concrete formulas land in step 2's cycle.)

Plus a small set of helper named composites (`copyReg`, `addRegConst`,
`zeroReg-via-decrement-loop` if `decReg` is used in place of
`zeroReg` for some purpose; `mvRegToReg`).

### §6.2 `KSimSubroutinesURM.lean` — K^sim realizations of URM primitives

Used by the URM → K^sim simulator (step 9). Each entry is a
K^sim subroutine that, given a packed register-state
encoding, returns the encoding after one URM step under that
primitive. Per Appendix A.3 of
`docs/lawvere-k-sim-hierarchy.md`, the K^sim PC-dispatch
uses `switch` (Tourlakis 2018 §0.1.0.17 (6), a fixed level-1
K^sim function); register updates per primitive are
level-≤-1 K^sim composites.

---

## §7 The simulator (erToK side)

Under Path 2, only one simulator direction is built: URM →
K^sim, used by `erToK` per Tourlakis 0.1.0.43-44 ⊇. The
URM → ER simulator from the Path-1 design is no longer
built (kToER goes K^sim → ER directly via §3).

### §7.1 K^sim simulator for URM

Per Appendix A.3 of `docs/lawvere-k-sim-hierarchy.md`. For
each URM `P`, build a K^sim term `simulateInKSim P :
KSimMorN (1 + P.numRegs) P.numRegs` that, given a time
bound and initial register values, yields the register
values after that many URM steps. Implementation: K^sim
`simrec` over time, with PC-dispatch via `switch` (Tourlakis
§0.1.0.17 (6), a fixed K^sim_1 function), and per-
instruction K^sim subroutines from §6.2 catalogue.

The K^sim simulator's level is ≤ 2: the simrec is at level
2 (children at level ≤ 1), the per-instruction step is at
level ≤ 1 (uses `switch` which is level 1 plus level-0
register updates), and PC-dispatch via `switch`-tree
composes level-1 functions.

### §7.2 Simulator interp-preservation

```lean
theorem simulateInKSim_interp
    (P : URMProgram)
    (outReg : Fin P.numRegs)
    (timeBound : ℕ) (regs : Fin P.numRegs → ℕ) :
  ((simulateInKSim P) outReg).interp (timeBound, regs)
    = runReg P.toRegisterMachine regs timeBound outReg
```

Proof: by induction on `timeBound`, with the inductive step
using `runReg_succ` (existing in `RegisterMachine.lean`)
plus the per-instruction interp lemmas (one per URM
primitive, in §6.2 `KSimSubroutinesURM.lean`).

---

## §8 The compiler (erToK side)

Under Path 2, only one compiler direction is built: ER →
URM. The Path-1 K^sim → URM compiler is no longer built
(kToER goes K^sim → ER directly via §3).

### §8.1 ER → URM compiler

```lean
def compileER : ∀ {a : ℕ}, ERMor1 a → URMProgram
  | _, .zero      => urmSubrZero  ...
  | _, .succ      => urmSubrSucc
  | _, .proj i    => urmSubrProj i
  | _, .sub       => urmSubrSub
  | _, .comp f gs => urmSubrComp (compileER f) (gs.map compileER)
  | _, .bsum f    => urmSubrBsum (compileER f)
  | _, .bprod f   => urmSubrBprod (compileER f)
```

One-line per ER constructor; each line invokes a catalogue
entry or combinator from §6.1.

### §8.2 Compiler interp-preservation

```lean
theorem compileER_URMComputes
    {a : ℕ} (e : ERMor1 a) :
  (compileER e).URMComputes_for e.interp
```

The aggregate `URMComputes` instance is built by structural
recursion on `e`: each ER constructor case applies the
catalogue entry's `URMComputes` and the relevant composition
combinator's `URMComputes`. By the design of §4.4 and §5,
this is mechanical; no global dominance argument needed.

---

## §9 The runtime-bound function (erToK side)

Under Path 2, the runtime bound is needed only for the
`erToK` direction (where the URM compiled from an ER term
runs in K^sim_2 time, per Ritchie–Cobham). The Path-1
`boundExpr f : ERMor1 a` (bounding K^sim_2 → URM runtime in
ER) is no longer built — kToER goes K^sim → ER directly via
§3 with `A_n^r` bounds, no URM compilation step.

### §9.1 `boundExprK e : KMor1 a` for the erToK URM runtime

For each `e : ERMor1 a`, construct
`boundExprK e : KMor1 a` of level ≤ 2 satisfying
`(compileER e).URMComputes.stepBound v ≤
(boundExprK e).interp v` for all `v`.

Shape: `tower h_e (vMax v + offset_e)` constructed in K^sim
using `2^x ∈ K^sim_2` per Tourlakis §0.1.0.17 (c). Both
`h_e` and `offset_e` are Lean `Nat`-valued functions of
`e`'s structure, computed bottom-up. The tight target is
`h_e ≤ 2` for every ER term `e`.

Per-ER-constructor arithmetic (concrete formulas in step 9's
cycle):

- **Atoms** (`zero`, `succ`, `proj`, `sub`): `h_e = 0`,
  small constant offset.
- **`comp f gs`**: tower-height arithmetic of children;
  combined via Module A's `tower_succ_pow_bound_strong`.
- **`bsum f`** and **`bprod f`**: per Module A's
  `polynomial_iter_tower_bound`, the iteration produces
  `tower 2`-bounded values; `h_e` rises to 2 (and stays
  there for nested invocations).

Reuse of existing infrastructure:

- `Utilities/ComputationalComplexity.lean`: `tower`,
  `tower_succ_pow_bound` (sequential composition tower-
  jump), `polynomial_iter_tower_bound` (loop-induced bound
  landing in `tower 2`), `tower_succ_pow_bound_strong`
  (height-fixed variant for `h ≥ 2`).
- K^sim already has `2^x ∈ K^sim_2` per Tourlakis
  §0.1.0.17 (c); the Lean realisation is a named composite
  built from `succ`/`proj`/`simrec` plus the linear
  arithmetic at level 1.

### §9.2 Why `boundExprK e` is in K^sim_2

The arithmetic `tower h_e (vMax v + offset_e)` for `h_e ≤
2` is constructed directly in K^sim using:

- `vMax v` via iterated `max` (a level-1 K^sim function).
- `2^x` via simrec (level 2 in K^sim per Tourlakis 0.1.0.17
  (c)). Iterating up to height 2 stays at level 2 by closure
  of K^sim under composition (which is level-preserving by
  K^sim's grading rule for non-simrec compositions).
- The additive shift is comp with succ, level 0.

The construction is direct (no Grzegorczyk-hierarchy
intermediates).

---

## §10 The functors and interp-preservation

### §10.1 `kToER` (Path 2 — see §3.5)

`kToER : KMor1 a → KMor1.level f ≤ 2 → ERMor1 a` is defined
in §3.5 by structural induction on K^sim, using
`simultaneousBoundedRec` plus the `A_n^r` majorant from
§3.4. `kToER_interp`, `kToERN`, `kToERN_interp`,
`kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat` and the
functor laws live in `LawvereKSimER.lean` (step 5's cycle
output). Refer to §3.5 for the full Path 2 specification.

### §10.2 `erToK` (URM-simulation side)

`erToK : ERMor1 a → KMor1 a` of level ≤ 2 is built by
composing §8 (ER → URM compiler), §7 (URM → K^sim
simulator), and §9 (K^sim runtime bound):

```lean
def erToK {a : ℕ} (e : ERMor1 a) : KMor1 a :=
  let P := compileER e
  let sim := simulateInKSim P
  -- wire: time = boundExprK e; inputs = projections;
  -- working / output regs = zeros; project final outputReg.
  KMor1.comp (sim P.outputReg)
             (boundExprK e, projections, zero-padding)
```

with level ≤ 2 by composition of K^sim_2 components.

### §10.3 `erToK_interp`

```lean
theorem erToK_interp
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
  (erToK e).interp v = e.interp v
```

Proof: by composing `simulateInKSim_interp` (§7.2) and
`compileER_URMComputes` (§8.2), with the runtime bound
`boundExprK e` ≥ `compileER e`'s `stepBound` (§9.1) ensuring
the simulator's truncation does not fire.

### §10.4 Functor lifts

`kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat`: per §3.5.

`erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2`:

- `obj n := n` (identity on objects).
- `map ⟦e⟧ := ⟦erToK e, level_proof⟧` — well-defined on
  quotient classes by `erToK_interp` (extensional
  equality propagates through the URM-simulation chain).
- Functor laws via `erToK_interp` plus the morphism-
  quotient setup.

---

## §11 The categorical isomorphism

### §11.1 Strict equality of round-trip functor compositions

```lean
theorem kToERFunctor_erToKFunctor :
  kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)
theorem erToKFunctor_kToERFunctor :
  erToKFunctor ⋙ kToERFunctor = 𝟭 LawvereERCat
```

Both hold as propositional functor equalities (Lean
`Functor.ext`-witnessed via `Quotient.sound` from
interp-equality, not as definitional `rfl`) because:

1. `obj` fields agree: all four functors are identity on objects
   (both categories have ℕ as objects, and our functors use
   `obj n := n`).
2. `map` fields agree: for any morphism class `⟦f⟧`,
   `(F ⋙ G).map ⟦f⟧ = G.map (F.map ⟦f⟧)`. By interp-preservation
   of both `F` and `G`, this morphism class has the same
   interpretation as `⟦f⟧`. Since the morphism categories are
   quotients by extensional-equality of interpretations,
   "same interpretation" = "same morphism". Hence
   `(F ⋙ G).map ⟦f⟧ = ⟦f⟧ = 𝟭.map ⟦f⟧`.

The proof reduces to one application of interp-preservation per
direction plus quotient-class-equality from interp-equality.

### §11.2 Equivalence wrapper

```lean
def lawvereERCatEquivKSimCat2 : LawvereERCat ≌ LawvereKSimDCat 2 :=
  -- via mathlib `equivOfIso` (or equivalent constructor)
  -- with the strict functor equalities lifted to nat isos
  -- via `eqToIso`.
  CategoryTheory.Equivalence.mk
    erToKFunctor kToERFunctor
    (eqToIso erToKFunctor_kToERFunctor.symm)
    (eqToIso kToERFunctor_erToKFunctor)
```

(Exact mathlib API to be pinned during step 11.)

### §11.3 Why iso, not just equivalence

The strict iso (functor-equality round-trip) gives strictly more
structural information than the bare equivalence. Anything proved
for `LawvereKSimDCat 2` morphisms (e.g. categorical limits, products,
structural lemmas) transports along the iso without natural-
transformation-coherence overhead.

---

## §12 Module file layout

Existing landed (no changes to load-bearing path):

```text
GebLean/Utilities/RegisterMachine.lean       (abstract kernel; reused)
GebLean/Utilities/Tower.lean                 (tower function + lemmas)
GebLean/Utilities/ComputationalComplexity.lean   (Module A)
GebLean/LawvereERPolynomialBound.lean        (Module B; PolyBound)
GebLean/Utilities/KSimSzudzikSimrec.lean     (Szudzik infrastructure;
                                              the kSimPackedBase/Step
                                              and kSimTowerBound parts
                                              remain dead code from
                                              the renamed direct path)
GebLean/LawvereKSim.lean
GebLean/LawvereKSimInterp.lean
GebLean/LawvereKSimQuot.lean
GebLean/LawvereKSimCat.lean                  (Phase 1 K^sim category)
GebLean/LawvereERQuot.lean
GebLean/Utilities/ERArith.lean
GebLean/Utilities/ERTreeArith.lean
GebLean/LawvereKSimERDirect.lean             (renamed direct-translation;
                                              level-0 and level-1
                                              dominance results retained
                                              as valid mathematics)
GebLean/LawvereKSimPolynomialBound.lean      (KMor1.linearBound; level-0
                                              and level-1 dominance;
                                              level0Shape; ConstantOrShiftedProj)
```

New files (proposed):

For the kToER side (Path 2 — structural induction):

```text
GebLean/Utilities/Tupling.lean                       [step 1]
  Nat.tuplePack, Nat.tupleAt, bijection theorems,
  polynomial value bound on packed tuple.

GebLean/Utilities/ERTupling.lean                     [step 1]
  ERMor1.tuplePack, ERMor1.tupleAt; PolyBound builders;
  interp lemmas; LawvereERCat.tupleIso.

(K^sim-side tupling NOT BUILT under Path 2; see §3.1.)

GebLean/Utilities/ERSimultaneousBoundedRec.lean      [step 2]
  ERMor1.simultaneousBoundedRec (multi-output ER bounded
  recursion); packs the (k+1)-tuple internally via
  Nat.tuplePack, recurses via single-output boundedRec,
  unpacks via Nat.tupleAt.  Interp lemma + PolyBound builder.

GebLean/Utilities/ERAMajorants.lean                   [step 3]
  ERMor1.A_one (interp λx.2x+2);
  ERMor1.A_one_iter (r-fold composition; interp A_1^r);
  ERMor1.A_two_iter alias of ERMor1.towerER (interp A_2^r);
  PolyBound builders for A_one and A_one_iter only
  (A_two_iter is tower-fast; no PolyBound).

GebLean/LawvereKSimMajorization.lean                 [step 4]
  KMor1.majorize_by_A_n_iter (Tourlakis 0.1.0.10 transcribed);
  linearBound_le_A_one_iter translation lemma reusing
  existing kToERDirect_linearBound_dominates_level_zero
  and _level_one for levels 0 and 1.

GebLean/LawvereKSimER.lean                           [step 5]
  kToER (structural induction on K^sim using
  simultaneousBoundedRec + A_n^r majorant);
  kToER_interp, kToERN, kToERN_interp;
  kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat;
  functor laws.  (Bare name, distinct from
  LawvereKSimERDirect.lean.)
```

For the erToK side (URM simulation):

```text
GebLean/Utilities/URMConcrete.lean                   [step 7]
  URMInstr (6 primitives), URMProgram, toRegisterMachine,
  URMComputes structure, urmSeq / urmIf / urmLoop combinators
  with stepBound and tower-witness arithmetic.

GebLean/Utilities/URMSubroutinesER.lean              [step 8]
  Catalogue of URM subroutines emulating each ERMor1
  constructor, each with URMComputes.  Used by ER → URM
  compiler.

GebLean/Utilities/KSimSubroutinesURM.lean            [step 9]
  Catalogue of KMor1 subroutines emulating each URM
  primitive, plus PC-dispatch combinator (via switch) and
  simulateInKSim assembly.  Per Appendix A.3 of
  docs/lawvere-k-sim-hierarchy.md.

GebLean/LawvereERKSim.lean                           [step 10]
  compileER : ERMor1 a → URMProgram (one-line match over ER
  constructors); boundExprK : ERMor1 a → KMor1 a (level ≤ 2);
  erToK; erToKN; erToK_interp;
  erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2;
  functor laws.
```

For the categorical iso:

```text
GebLean/LawvereERKSimEquivalence.lean                [step 11]
  Strict iso erToKFunctor ⋙ kToERFunctor = 𝟭, and reverse.
  Mathlib Equivalence wrapper.
```

Module dependency graph:

```text
kToER side:
  Tupling ─→ ERTupling ─→ ERSimultaneousBoundedRec ─┐
       (KSimTupling not built — see §3.1)
                                                     ├─→ LawvereKSimER
       ERAMajorants ─→ LawvereKSimMajorization ──────┘
                            ↑
       (existing) LawvereKSimPolynomialBound (for the
                  linearBound dominance theorems reused
                  via translation)

erToK side:
  RegisterMachine ─→ URMConcrete ─┬─→ URMSubroutinesER ─┐
                                  └─→ KSimSubroutinesURM ┴─→ LawvereERKSim

Both:
  LawvereKSimER  ─┐
  LawvereERKSim  ─┴─→ LawvereERKSimEquivalence
```

Re-exports updated in `GebLean.lean` per the project's policy.

---

## §13 Reuse pointers

### §13.1 Direct reuse (load-bearing path)

- **`RegisterMachineNS.RegisterMachine` (structure)** —
  used by `URMConcrete.toRegisterMachine` (§4.3).
- **`RegisterMachineNS.run`, `runFromConfig`, `runReg`** and their
  reduction lemmas — used in `URMComputes.correct` and simulator
  interp proofs (§7.2).
- **`RegisterMachineNS.ElementaryBound`** — derived from
  `URMComputes.toElementaryBound` (§4.5).
- **`Utilities/Tower.lean`'s `tower`, `tower_zero`,
  `tower_succ`** — used in `URMComputes.towerDominates` and
  in simulator value-bounds.
- **`Utilities/ComputationalComplexity.lean`'s
  `tower_succ_pow_bound`** — `urmSeq` tower arithmetic (§5.1).
- **`Utilities/ComputationalComplexity.lean`'s
  `polynomial_iter_tower_bound`** — `urmLoop` tower
  arithmetic (§5.3).
- **`LawvereERPolynomialBound.lean`'s `ERMor1.PolyBound` and
  builders** — used by Path 2 kToER for the `A_n^r` named
  composites (§3.3) and for ER expressions internal to
  `boundExprK e`'s K^sim construction (§9).
- **`LawvereERPolynomialBound.lean`'s
  `ERMor1.PolyBound.log_le_towerHeight`** — bridging ER tower
  expressions to value bounds when needed.
- **`Utilities/KSimSzudzikSimrec.lean`'s `kSimSzudzikPackList`,
  `kSimSzudzikUnpackAt`, `seqPackBound`** — encoding URM
  register vectors and PCs as a single ℕ for the simulator's
  iteration state (§7.1).
- **`Utilities/ERArith.lean`'s `pred`, `discN`, `boundedRec`** —
  used by ER's runtime-bound construction (§9) and by the
  ER side of the structural induction (§3).
- **`LawvereKSim.lean`, `LawvereKSimInterp.lean`,
  `LawvereKSimQuot.lean`, `LawvereKSimCat.lean`** — Phase 1
  K^sim source / target infrastructure.
- **`LawvereERQuot.lean`, `LawvereKSimQuot.lean`** — quotient
  categories for the functor lift (§10.3).

### §13.2 Indirect reuse (cross-checks and witness validation)

- **`LawvereKSimERDirect.lean`'s
  `kToERDirect_interp_level_zero`,
  `kToERDirect_interp_level_one`** — independent witnesses that
  level-0 and level-1 K^sim functions are computable in ER;
  cross-checking the URM-route's correctness on small cases.
- **`LawvereKSimPolynomialBound.lean`'s `KMor1.linearBound`,
  `level0Shape`, `ConstantOrShiftedProj`** — cross-checking that
  the URM-runtime tower bound on level-1 K^sim agrees with the
  direct-translation linear bound on the same inputs.
- **`Phase4Investigation.lean`** — landed witnesses such as
  `addKFanOut5`, usable as test inputs for the new pipeline.

### §13.3 Test scaffolding

The K^sim primitives `addK`, `addKFanOut5`, and the level-0
/ level-1 atomic constructors all have known interpretations.
Step 4's catalogue can be tested with `#guard` on these
representatives at each cycle.

---

## §14 Citation map

The literature uses `E^n` notation (Grzegorczyk hierarchy);
our project uses `ER` directly per `GebLean/LawvereER.lean`'s
inductive (see §1.4). The references below are catalogued in
the literature's original `E^n` notation. Per §1.4, every
load-bearing claim using `E^n` in the literature is realized
in our project as a direct construction in `ERMor1`; no
proof step depends on the ER ↔ E^n equivalence.

### §14.1 Tourlakis 2018 (file `PR-complexity-topics.pdf`)

- **§0.1.0.7** — K^sim definition.
- **§0.1.0.15** — K^sim_n = L_n.
- **§0.1.0.17** (esp. clauses (c), (6)) — worked examples in
  K^sim, including the `switch` construct.
- **§0.1.0.22** — Grzegorczyk hierarchy definition.
- **§0.1.0.27** (esp. clauses (1)–(4)) — Bounding Lemma for E^n.
- **§0.1.0.34** — E^2 closed under bounded recursion;
  pairing in E^2 (Tourlakis's witness is Cantor's `J`; we
  use Szudzik's `Nat.pair`, see §3.1 note).
- **§0.1.0.39** — URM-simulating functions in K_4
  (corollary to §0.1.0.37). Not directly used by the design;
  noted here for completeness.
- **proof of §0.1.0.43, pp. 19-21** — Loop-to-URM translation
  with worked examples (`λx.x`, `λx.x+1`, `λxy.x·y`,
  Loop-to-URM template, bounded-recursion URM template).
- **§0.1.0.43** — Ritchie-Cobham property of E^n.
- **§0.1.0.44** — K^sim_n = E^{n+1} for n ≥ 2.

### §14.2 Tourlakis CN (file `tourlakis-Computability-Notes-ROOT.pdf`)

- **§4.2.2** — Hilbert-Bernays sequence-number coding.
- **§10.2.20** — cross-reference for K^sim_n = E^{n+1}.

### §14.3 Other literature

- **Cutland Theorem 4.1.1** (cited via Damnjanovic 1994 §1) —
  programs in standard formalisms compute exactly the
  elementary functions, with elementary time/space bounds.
- **Davis-Weyuker chapter 13** — explicit RM ↔ LOOP
  correspondences with simulators.
- **Meyer-Ritchie 1967** — original `LOOP_n = E^{n+1}` proof.
- **Damnjanovic 1994 §4 Lemma 3.1** — `f_k` tower-bound
  inequalities for LOOP programs (cross-checking material if
  the URM-runtime bound shape mirrors `f_k`).

### §14.4 Internal references

- **`docs/lawvere-k-sim-hierarchy.md` Appendix A** — erToK
  URM-simulation design (steps 7-10 mirror this).
- **`docs/research/2026-04-30-ksim-polynomial-bound-references.md`** —
  tower-bound shape rationale; Module A/B salvage list.
- **`docs/research/2026-05-02-ksim-to-er-architectural-pivot-handoff.md`** —
  the pivot decision and prior-failure catalogue.

---

## §15 Adversary's punch list for step 0

The step-0 adversarial brainstorm + sequential-thinking review
must explicitly check the following claims, each derived from a
prior-failure-mode hypothesis. The adversary is obligated to
follow literature references and either confirm or reject each
claim; rejection forces design revision.

### §15.1 Was the prior failure mode value-bound (not runtime-bound)?

Claim: The prior strategy (`kToERDirect`) tried to bound K^sim
function values pointwise by an ER expression. The new strategy
bounds URM step counts. These are different objects and the
shift removes the trap.

Adversary obligation: verify by reading `kSimTowerBound` and
`kSimTowerBound_dominates_inline` (in
`Utilities/KSimSzudzikSimrec.lean` and
`LawvereKSimPolynomialBound.lean`); confirm that the
`towerDominates` field of the new `URMComputes` structure
genuinely concerns step counts and not function values.

### §15.2 Does either side of Path 2 recreate the prior trap?

Claim (kToER, structural-induction side): The new bound shape
is Tourlakis's `A_n^r` (a sequence of explicit ER named
composites: `A_one`, `A_one_iter`, `A_two_iter`). Composition
of A_n^r bounds via `simultaneousBoundedRec` encapsulates the
packing arithmetic: at K^sim levels ≤ 1 the packed-state
bound is polynomial-shape (consumed via the
`ofSimultaneousBoundedRec` PolyBound builder); at level 2
the packed-state bound is tower-shape, derived at the Nat
level from step 4 majorization and fed to
`simultaneousBoundedRec_interp_correct` as a dominance
hypothesis (no PolyBound builder invoked). In both regimes
the packing and unpacking happen inside
`simultaneousBoundedRec`, never visible at the kToER outer
level. No `3^E` coefficient leaks out.

Claim (erToK, URM side): URM step counts are computed by
combinators that are additive (`urmSeq`, `urmIf`) or sum-of-
iterations (`urmLoop`); none introduce an exponential
coefficient analogous to the prior `3^E`.

Adversary obligation: spot-check the §3.4 majorization
arithmetic (Nat-level iteration on `A_n^r` bounds, kToER
side) and §3.2's `simultaneousBoundedRec` polyBound (used
at K^sim levels ≤ 1); spot-check the §5 combinator
arithmetic table (erToK side). Trace whether any
coefficient appears in either side that would force a
prior-style absorption inequality.

### §15.3 Is ER → URM compilation closed in ER (erToK side)?

(Note: under Path 2, K^sim_2 → URM compilation is NOT part
of any path; kToER goes directly K^sim_2 → ER via
structural induction. This punch-list item now applies only
to the erToK side's ER → URM compilation.)

Claim: The `compileER` compiler, applied to any ER term,
produces a URM whose `URMComputes.towerHeight` is bounded
appropriately for the `boundExprK e` runtime bound to
remain in K^sim_2 (level ≤ 2). The compiler does not
implicitly require K^sim_3 features (e.g. unbounded
`condJump` patterns smuggled in via the `bsum`/`bprod`
combinators).

Adversary obligation: trace the `bsum`/`bprod` cases of
`compileER` (§8.2) to confirm the produced URM uses
`condJump` only on bounded counter registers, never on
unbounded-iteration patterns. Verify that the `urmLoop`
combinator's tower-height contribution per `bsum`/`bprod`
nesting matches the K^sim_2 closure under bounded
recursion.

### §15.4 Is the level-1-vs-level-2 asymmetry from prior plan v5 absent (Path 2 kToER)?

Plan v5's failure mode: the level-1 dominance chain in
`kToERDirect` worked because of a level-0-specific shape
assumption (`level0Shape.linearBound.1 ≤ 1`) that did not
lift to level-1 children of a level-2 simrec. Path 2 must
verify this asymmetry does not recur.

Claim: Path 2's `KMor1.majorize_by_A_n_iter` is uniform
across K^sim levels via structural induction. The level-2
case is proven via Nat-level iteration arithmetic on
`A_1^r` bounds for K^sim_1 children, yielding an
`A_2^{r'}` bound on the simrec output (a Nat inequality,
not a PolyBound). The level-1 children's bound is `A_1^r`
(explicit polynomial), not the prior
`linearBound`/`level0Shape`-specific shape.  The
multi-output simrec is handled by
`simultaneousBoundedRec`'s ERMorN interface; the packing
arithmetic is encapsulated and the resulting per-component
bound shape does not depend on level-0 specifics.

Adversary obligation: trace §3.4's level-2 majorization
proof. Verify that the recursive call applies to children
at K^sim_1 with NO additional shape constraint beyond
"K^sim level ≤ 1 hence bounded by `A_1^r` for some r".
Verify that the level-2 majorization arithmetic
(Nat-level) takes any `A_1^r`-bounded children and
produces an `A_2^{r'}`-bounded result for explicit r'.
(`A_2^{r'}` is tower-fast and has no PolyBound; the
result is a Nat inequality, fed to
`simultaneousBoundedRec_interp_correct`'s dominance
hypothesis at step 5, not to `ofSimultaneousBoundedRec`.)
If any step requires a level-0-specific assumption,
that's a defect and the prior failure mode has recurred.

### §15.5 Is the categorical iso of step 11 strict, not natural?

Claim: `kToERFunctor ⋙ erToKFunctor = 𝟭 (LawvereKSimDCat 2)` holds
strictly (functor equality), not merely up to natural
isomorphism. The argument relies on:
(a) both functors being identity on objects;
(b) interp-preservation pointwise for all morphisms;
(c) the morphism categories being quotients by interp-equality.

Adversary obligation: verify (a) by inspecting the proposed
`kToERFunctor.obj` and `erToKFunctor.obj` definitions; verify
(b) by checking the proof outlines for `kToER_interp` and
`erToK_interp` (§10.2); verify (c) by reading
`LawvereKSimQuot.lean` and `LawvereERQuot.lean`.

### §15.6 Per-URM construction matches Tourlakis (erToK only)

(Note: under Path 2, this item applies only to the erToK
side, where Path 1's URM-simulation design is preserved.
The kToER side does not use URM at all.)

Claim: Tourlakis 2018's proof of §0.1.0.43 (Ritchie–Cobham)
constructs URMs per function (not a single universal URM)
and the corresponding simulating function in the target
language is per-URM. The erToK side adopts per-URM
construction by symmetry with Tourlakis.

Adversary obligation: verify by reading
`PR-complexity-topics.pdf` pp. 19-22 directly. Confirm the
worked examples (`λx.x`, `λx.x+1`, `λxy.x·y`, the Loop-to-
URM template, the bounded-recursion URM template) are all
per-program / per-function. Check the §0.1.0.44 ⊇ proof
for the per-M phrasing.

### §15.7 Are the catalogue obligations local?

Claim: Each catalogue entry's `URMComputes` proof is local — it
references only the entry's own definition, the `tower` and
`runReg` lemmas from `RegisterMachine.lean`, and possibly
sub-catalogue entries via composition combinators. No global
dominance argument is required.

Adversary obligation: spot-check 2-3 catalogue entries (e.g.
`urmSubrKSucc`, `urmSubrKSimrec`, `erInstrCondJump`); trace the
sketch of their `URMComputes` proofs to confirm locality. If any
entry requires reasoning about other entries beyond the
combinator interface, that is a defect.

### §15.8 Is the design constructive throughout?

Claim: No use of `Classical`, `noncomputable`, or `axiom`. All
existence claims (e.g. termination of catalogue subroutines) are
witnessed by explicit Lean functions (e.g. `URMComputes.stepBound`).

Adversary obligation: review the `URMComputes` structure for any
existential field; review the proposed simulator constructions
for any Classical-dependent operation; confirm that the Szudzik
encoding, `boundedRec`, and `simrec` constructions remain
constructive.

### §15.9 Is interpretation-preservation strict?

Claim: `kToER_interp` and `erToK_interp` are equalities at the
interpretation level (`(F f).interp v = f.interp v`), not
inequalities or "dominated by" claims.

Adversary obligation: confirm the theorem statements in §10.2
and §10.4 are equalities; trace the proof outlines for absence
of inequalities at the ouput of the simulator.

### §15.10 Are the kToER and erToK halves genuinely independent?

Claim: The kToER side (steps 1-5, structural induction Path
2) does not depend on the erToK side (steps 6-10, URM
simulation), and vice versa. Step 11 depends on both.

Adversary obligation: verify the dependency graph (§12)
shows no cycle or backward edge from kToER-load-bearing
modules to erToK-load-bearing modules.

### §15.11 Does any Lean proof depend on ER ↔ E^n?

Claim: Per §1.4 and §1.5, this project formalizes `ER`
directly per `GebLean/LawvereER.lean` and does **not**
formalize the Grzegorczyk hierarchy. The chain of Lean
theorems on the kToER side
(`KMor1.majorize_by_A_n_iter`, `kToER_interp`,
`kToERFunctor`'s functor laws), the chain on the erToK
side (`compileER`'s correctness, `simulateInKSim_interp`,
`erToK_interp`, `erToKFunctor`'s functor laws), and the
strict-iso equalities at step 11 close `K^sim_2 ⊆ ER` (and
reverse) by direct construction, without ever stating or
proving any of:

- Tourlakis 2018 §0.1.0.43 (Ritchie–Cobham);
- Tourlakis 2018 §0.1.0.44 (`K^sim_n = E^{n+1}`);
- Tourlakis 2018 §0.1.0.27 (bounding lemma for `E^n`);
- Tourlakis 2018 §0.1.0.22 (Grzegorczyk hierarchy);
- the ER ↔ E^3 function-class equivalence;
- any closure property of `E^n` for any `n`.

Literature references using `E^n` notation appear only in
the citation map (§14), in motivation prose (§1.2, §3.4,
§3.6, §5.4, §9), and in §1.4 / §1.5 explaining the
discipline itself. None of those references is converted
into a Lean lemma or used as a black-box step.

Adversary obligation 1 (every E^n occurrence is non-load-
bearing): trace each `E^n` occurrence in the document;
confirm that for every occurrence, the surrounding context
either (a) is in §1, §14, or another non-load-bearing
section, or (b) restates the same claim in `ER` terms with
a direct `ERMor1` construction. Any place where the proof
chain steps from "X is in `E^n`" to "X is in `ER`" without
going through a direct `ERMor1` term is a defect.

Adversary obligation 2 (no Lean lemma reuses Tourlakis's
E^n proof verbatim): trace each Lean theorem listed under
§1.5's "What we implement" bullets; confirm its proof
outline (per §3, §7, §8, §9, §10 of this document, plus
the per-cycle plans to be written) is a direct construction
or induction on `ERMor1` / `KMor1` / `URMProgram` /
`URMComputes`, **not** a transcription of a Tourlakis
proof. Particular spot-checks:
`KMor1.majorize_by_A_n_iter` must not invoke "E^n closure
under bounded recursion" beyond what we have proven for
ER's `boundedRec`; `simulateInKSim_interp` must not appeal
to "the simulating function for the output variable of M"
as a known fact (we construct it as a Lean term, not cite
it from Tourlakis 0.1.0.37); the level-2 majorization
proof must not invoke 0.1.0.27's bounding lemma as a black
box.

Adversary obligation 3 (the A_n named composites are direct
ER terms): spot-check §9.2 (erToK side) and §3.3, §3.4
(kToER side) "stays in ER" arguments; confirm that the
constructions of `A_one`, `A_one_iter`, `A_two_iter`, and
the K^sim runtime bound `boundExprK e` do not rely on any
Grzegorczyk-hierarchy fact. Each must have a `@[simp]
interp` lemma traceable to existing ER named composites
(`addN`, `succ`, `expER`, `towerER`).

Adversary obligation 4 (no Path-1 packing scaffolding leaks
into Path 2): spot-check §3.5's `kToER` simrec case,
confirming it uses `simultaneousBoundedRec` with an
`A_n_iter`-shaped majorant — not `kSimTowerBound`,
`kSimPackedStep`, `kSimPackedBase`, or any other artifact
of the kToERDirect path. Those names should appear nowhere
in the kToER side's Lean theorems.

If any spot-check fails, the master design must be revised
before any cycle proceeds.

### §15.12 Path 2 specific — Tupling stays in ER at all levels

Claim: The fixed-length Szudzik pairing
(`Nat.tuplePack k` packing `(k+1)`-tuples,
`ERMor1.tuplePack k`) and its inverse
(`Nat.tupleAt k`, `ERMor1.tupleAt k`) are in ER and have
polynomial value bounds, with

```text
tuplePack k v ≤ tuplePackCoef k * (M + 1)^{2^k}
```

for `M = max v` over `Fin (k+1)`, where
`tuplePackCoef : ℕ → ℕ` is the computable Lean function
`tuplePackCoef 0 = 1`, `tuplePackCoef (k+1) = (tuplePackCoef k + 2)^2`
(derived from the underlying recurrence `B_0 = M`,
`B_{k+1} ≤ (M + B_k + 1)^2`, per §3.1). For each fixed
`k`, this is a polynomial of fixed degree `2^k` in inputs;
ER's `PolyBound` infrastructure certifies it directly with
`degree = 2^k`, `coefficient = tuplePackCoef k`,
`constant = 0`.

Adversary obligation: verify the recursive definition of
`tuplePack` and `tupleAt` against §3.1. Confirm the
`PolyBound` builders compose correctly (`k = 0` is the
identity 1-tuple at degree 1; `k+1` via Szudzik `pair`
squares the degree, accumulating to degree `2^{k+1}` per
the recurrence — a fixed polynomial for each fixed `k`).

### §15.13 Path 2 specific — `simultaneousBoundedRec` packing is encapsulated

Claim: `ERMor1.simultaneousBoundedRec` packs the (k+1)-tuple
of intermediate values via `Nat.tuplePack` internally. When
the per-component bound is itself polynomially bounded
(K^sim levels ≤ 1), the packing arithmetic produces a
polynomial-shape value bound on the packed state, surfaced
through the `ofSimultaneousBoundedRec` PolyBound builder.
At level 2 the per-component bound is `A_2^r` (tower-fast)
and has no PolyBound; the level-2 chain consumes a
Nat-level dominance hypothesis directly via
`simultaneousBoundedRec_interp_correct` and does not
invoke the PolyBound builder. The output is `ERMorN`;
downstream `kToER` sees a clean ERMorN multi-output
interface and never sees the packing's coefficient. No
`3^E`-style coefficient leaks out of
`simultaneousBoundedRec`'s implementation.

Adversary obligation: verify that
`simultaneousBoundedRec`'s `PolyBound` builder has a
polynomial-shape bound with degree depending only on `k`
(the simrec's component count) and on the per-component
PolyBound's degree, not on the source K^sim term's
overall structure. Compare against the prior
`kSimPackedStep_polyBound`'s `coefficient = 3^E` field;
the new bound must not have an analog. Verify that the
level-2 chain bypasses the PolyBound builder and instead
threads a Nat-level dominance hypothesis from step 4
through `simultaneousBoundedRec_interp_correct`.

### §15.14 Path 2 specific — `A_n^r` named composites are direct ER constructions

Claim: `ERMor1.A_one`, `ERMor1.A_one_iter`, and
`ERMor1.A_two_iter` are constructed directly using
existing ER named composites (`addN`, `succ`, `expER`,
`towerER`). `A_one` and `A_one_iter` carry `PolyBound`
builders certifying linear-shape bounds in inputs.
`A_two_iter` is the alias `towerER r`, already in ER by
its existing construction; no `PolyBound` exists for it
(`tower r x` is not polynomially bounded), and none is
needed by the level-2 chain.

Adversary obligation: verify the construction of
`A_one := comp addN [comp succ (proj 0), comp succ (proj 0)]`
(or equivalent) does not invoke any `E^n` closure. Verify
`A_two_iter` aliases existing `towerER` (which uses `expER`
as the closure step). Confirm the `PolyBound` builders for
`A_one` and `A_one_iter` compose with existing ER
constructor builders. Confirm that `A_two_iter` ships only
an interp routing lemma (delegating to `interp_towerER`)
and no `PolyBound` builder.

### §15.15 Path 2 specific — Majorization is per-K^sim-level structural induction

Claim: `KMor1.majorize_by_A_n_iter` is proven by structural
induction over K^sim levels. Levels 0 and 1 reuse existing
`kToERDirect_linearBound_dominates_level_*` theorems composed
with `linearBound_le_A_one_iter`. Level 2 is a fresh proof
using Nat-level iteration arithmetic on `A_1^r` bounds for
the K^sim_1 children of a level-2 simrec — not using the
prior `kSimTowerBound` shape (which had the `3^E`
coefficient that defeated v2-v5).

Adversary obligation: verify the proof outline for level-2
majorization in §3.4. Trace whether any step uses the prior
`kSimTowerBound`, `kSimPackedStep`, or related Szudzik-
packed scaffolding that previously failed. Confirm the
level-2 proof relies only on (a) Nat-level iteration
arithmetic over `A_1^r` bounds (step 4 majorization),
(b) `simultaneousBoundedRec_interp_correct` (the
Nat-hypothesis-driven correctness theorem; not the
`PolyBound` builder, which is unavailable at level 2
because `A_two_iter` has no `PolyBound`), and
(c) the `A_two_iter` interp simp lemma. None of these has
the prior trap's structure.

### §15.16 Path 2 specific — `kToER` is one-line per K^sim constructor

Claim: `kToER` is a single Lean function defined by
structural recursion on K^sim, with each constructor case a
one-line `match` invoking either a named composite (atoms,
comp, raise) or `simultaneousBoundedRec` with the A_n^r
majorant from `KMor1.majorize_by_A_n_iter` (simrec).

Adversary obligation: read the proposed `kToER` definition
(§3.5). Confirm each of the 6 K^sim constructor cases is a
one-line `match` invocation. If any case requires inline
auxiliary calculations beyond combinator application,
that's a defect (suggests missing infrastructure).

---

## §16 Notes for downstream cycles

### §16.1 Cycle hand-off shape

Each per-step cycle starts by reading this master design's
relevant sections, plus any per-step refinements written during
that cycle's brainstorm. Each cycle's writing-plans output is
filed as `docs/plans/2026-MM-DD-er-ksim2-equiv-step-N-<topic>.md`,
referencing this master document by section number.

### §16.2 Citation discipline reminder

Per CLAUDE.md "Literature-citation discipline (transcription
workstreams only)": every planned function, definition, or
theorem in any cycle's plan carries a literature reference;
every implemented entity carries the same reference in its
docstring. The references in §14 are the master list; cycles
refine to specific page or proof-step numbers.

### §16.3 Bottom-up named-composite discipline reminder

Per CLAUDE.md: never add a `KMor1`/`ERMor1`/`URMInstr` constructor
or downstream consumer before its image in the target language
has been built and named as a `def` (with a `@[simp]` interp
lemma where applicable). The four catalogues are the named-
composite layers for the four URM-boundary translations; the
compilers and simulators are the consumers.

### §16.4 Failure-mode escalation

If during a per-step cycle the adversarial review identifies an
obstacle that revisits a prior-failure-mode hypothesis (§15.1
through §15.16), pause and re-open this master design rather than
attempting to patch the per-step plan. The master design's
adversary-punch-list claims are the load-bearing assumptions of
the project; their invalidation is a master-level event.

---

End of master design.
