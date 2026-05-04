# `kToER` forward translation: design

## Status

Design document for Phase-2 sub-project 1 — the forward
translation `kToER : KMor1 → ERMor1` (restricted to K^sim
level ≤ 2).  Awaiting user review before writing the
implementation plan.

## Scope

Phase 2 of the K^sim hierarchy formalization is decomposed
into four sub-projects per the master design document
(`docs/lawvere-k-sim-hierarchy.md`):

1. Forward translation `kToER` (this sub-project).
2. URM concrete instructions and K^sim simulator term.
3. Ackermann/runtime bound for the URM simulator.
4. Backward translation `erToK` and the Phase-2 categorical
   equivalence packaging.

This sub-project produces `kToER`, its multi-output
companion `kToERN`, the interp-preservation theorems, and
the categorical functor `F : KSimMor 2 ⥤ LawvereERCat`.
A precondition refactor adjusts Phase 1's
`KMorNQuo.atDepth` from a Prop existential to a
data-bearing Setoid quotient so the functor's
representative extraction is constructive.

## References

- Master design: `docs/lawvere-k-sim-hierarchy.md`,
  particularly §2.3 (forward translation), §2.6
  (categorical packaging).
- Phase 1 plan and execution:
  `docs/plans/2026-04-29-lawvere-k-sim-phase1-plan.md`.
- Existing infrastructure: `ERMor1.boundedRec` and
  `boundedRec_eq_natRec_of_bounded` in
  `GebLean/Utilities/ERArith.lean`; `towerHeight`,
  `towerER`, `towerBound` in
  `GebLean/LawvereERBoundComputable.lean`; Szudzik
  utilities in `GebLean/Utilities/SzudzikSeq.lean`;
  Phase 1 K^sim machinery in `GebLean/LawvereKSim.lean`,
  `GebLean/LawvereKSimInterp.lean`,
  `GebLean/LawvereKSimQuot.lean`.

## Architecture

`kToER` is a structural recursion `KMor1 a → f.level ≤ 2
→ ERMor1 a` translating each K^sim constructor to an ER
composite.  The atomic constructors map directly; `comp`
and `raise` recurse; `simrec` at depth ≤ 2 (children at
depth ≤ 1) encodes the simultaneous-recursion vector via
Szudzik pairing and runs it via `ERMor1.boundedRec` with a
tower-height bound from `towerBound`.  A multi-output
`kToERN` lifts pointwise; a functor
`F : KSimMor 2 ⥤ LawvereERCat` lifts `kToERN` through the
K^sim and ER quotient categories.

The depth-witness refactor of Phase 1's
`KMorNQuo.atDepth` (Prop → Setoid-quotient with
data-bearing rep) is a precondition: without it,
extracting a level-≤-2 representative from a `KSimMor 2`
value requires `Classical.choice`, which the project
forbids.

## Components

### C1 — Refactor `KMorNQuo.atDepth`

Replace the Prop existential

    def KMorNQuo.atDepth (d : ℕ) (q : KMorNQuo n m) : Prop :=
      ∃ f : KMorN n m,
        (∀ i, (f i).level ≤ d) ∧ Quotient.mk _ f = q

with a data-bearing raw witness, an always-true Setoid,
and the Setoid-quotient:

    structure KMorNQuo.AtDepthRaw (d : ℕ)
        (q : KMorNQuo n m) where
      rep        : KMorN n m
      rep_level  : ∀ i, (rep i).level ≤ d
      rep_eq     : Quotient.mk (kMorNSetoid n m) rep = q

    instance kMorNQuoAtDepthSetoid (d : ℕ)
        (q : KMorNQuo n m) :
        Setoid (KMorNQuo.AtDepthRaw d q) where
      r _ _ := True
      iseqv := ⟨fun _ => trivial,
                fun _ => trivial,
                fun _ _ => trivial⟩

    def KMorNQuo.atDepth (d : ℕ) (q : KMorNQuo n m) :
        Type :=
      Quotient (kMorNQuoAtDepthSetoid d q)

All elements of `KMorNQuo.atDepth d q` are equal as Lean
values via `Quotient.sound trivial`, preserving the
proof-irrelevance behaviour of the original Prop
formulation, while constructive consumers can extract a
representative through `Quotient.lift`.

Update affected Phase-1 declarations:

- `KMorNQuo.id_atDepth`, `KMorNQuo.comp_atDepth`:
  change from `theorem` to `def`, producing
  `KMorNQuo.atDepth d (...)` values via
  `Quotient.mk _ ⟨..., ..., ...⟩`.
- `KSimMor.ext`: continue to take only a `hom`-equality
  hypothesis; the witness equality is supplied by
  `Quotient.sound trivial` after `subst`.
- `Category` instance on `LawvereKSimDCat d`: re-verify
  category laws (proofs structure unchanged; the witness
  components are quotient-equal).
- `KSimMor.includeSucc`: extract the rep via
  `Quotient.lift`, weaken `rep_level` via
  `Nat.le_succ_of_le`, repackage.

### C2 — `kToER`

    def kToER : {a : ℕ} → (f : KMor1 a) → f.level ≤ 2 →
        ERMor1 a

Per-constructor structural recursion:

- `KMor1.zero`: `ERMor1.zeroN a` (or analogous).
- `KMor1.succ`: `ERMor1.succ`.
- `KMor1.proj i`: `ERMor1.proj i`.
- `KMor1.comp f gs`: recurse on `f` and on each `gs i`
  (using the `max` rule on `level (comp f gs)` to
  derive sub-level bounds), assemble via
  `ERMor1.comp`.
- `KMor1.raise f`: identity on the underlying interp;
  recurse on `f` with the weakened bound derived from
  `level f + 1 ≤ 2`.
- `KMor1.simrec i h g`: at depth ≤ 2 the children are
  at depth ≤ 1, so we can recurse on each `h j` and
  `g j`.  Build the Szudzik-packed iterator via the
  helpers in C5.  Apply `ERMor1.boundedRec` with the
  tower bound from C5.  Compose with the Szudzik
  component projection at index `i`.

### C3 — `kToERN`

Multi-output companion:

    def kToERN : {a m : ℕ} → (f : KMorN a m) →
        (∀ i, (f i).level ≤ 2) → ERMorN a m

Pointwise: `(kToERN f h) i := kToER (f i) (h i)`.

### C4 — Interp-preservation theorems

    theorem kToER_interp {a : ℕ} (f : KMor1 a)
        (h : f.level ≤ 2) (ctx : Fin a → ℕ) :
        (kToER f h).interp ctx = f.interp ctx

    theorem kToERN_interp {a m : ℕ} (f : KMorN a m)
        (h : ∀ i, (f i).level ≤ 2) (ctx : Fin a → ℕ) :
        (kToERN f h).interp ctx = f.interp ctx

Proofs by structural induction on `f`.  Atomic and `comp`
cases reduce by interp-rewriting.  The `simrec` case
composes the property lemmas of the helpers in C5
(Szudzik round-trip, `boundedRec_eq_natRec_of_bounded`,
recursive interp hypotheses on `h j` and `g j`).

### C5 — Helpers in `GebLean/Utilities/`

The `simrec` case is the bulk of the work and decomposes
into named composites with interp-lemmas, per the
bottom-up named-composite discipline (CLAUDE.md) and
P10 (interpret-and-verify).  Targeted utilities:

- `kSimSzudzikPack : ERMor1 (k+1) → ERMor1 (k+1)`
  (or analogous) packing a (k+1)-tuple of ER values
  into a single ℕ via iterated Szudzik.  Each
  associated `_interp` lemma rewrites the packed
  value to its component-wise form.
- `kSimSzudzikUnpack : (i : Fin (k+1)) → ERMor1 1`
  selecting the `i`-th component from a Szudzik-packed
  value.  Round-trip lemma:
  `Unpack i ∘ Pack ⟨v_0, …, v_k⟩ = v_i`.
- `kSimPackedStep` builds the iterator step from the
  per-component `g_j_ER` translations and Szudzik
  pack/unpack.
- `kSimPackedBase` builds the base case from
  `h_j_ER`.
- `kSimTowerBound` selects the tower height from
  `towerHeight` applied to children, then composes
  `towerBound` to produce the ER bound term.

Place these in `GebLean/Utilities/KSimSzudzikSimrec.lean`
(or a similar utility module).  Each carries an
`@[simp]`-tagged interp lemma stating its closed-form
behaviour.

### C6 — Functor `F : KSimMor 2 ⥤ LawvereERCat`

    def kToERFunctor : KSimMor 2 ⥤ LawvereERCat where
      obj n := n
      map (h : KSimMor 2 n m) :=
        Quotient.lift
          (s := kMorNQuoAtDepthSetoid 2 h.hom)
          (fun raw =>
            Quotient.mk _ (kToERN raw.rep raw.rep_level))
          (proof_well_def)
          h.depth_witness
      map_id  := …
      map_comp := …

The well-definedness proof shows that any two raw
witnesses in the same Setoid (i.e. always-equivalent)
yield the same `ERMorNQuo` value.  Since both raw
witnesses' representatives map (under `kToERN`) to ER
terms with the same interpretation as `h.hom`'s
quotient class, they live in the same
`erMorNSetoid`-equivalence class, so their ER quotient
classes coincide.

### C7 — Tests

`GebLeanTests/LawvereKSimER.lean` with three tiers:

1. Per-constructor `#guard` spot-checks: applying
   `kToER` to `KMor1.zero`, `KMor1.succ`, `KMor1.proj`
   at small inputs and verifying the ER interp matches.
2. Round-trip on the existing `addK` from Phase 1
   (level-1 `simrec` for addition): `kToER addK h` is
   an ER term; `#guard` checks confirm its
   interpretation matches addition on test inputs.
   This exercises the `simrec` translation end-to-end.
3. Functor `F` sanity check: lift `addK` to a
   `KSimMor 2` value via the existing structure;
   apply `F.map`; extract a representative; verify
   its interp.  Exercises the data-bearing depth
   witness extraction path.

Helpers in C5 receive their own per-helper `#guard`
checks: Szudzik pack/unpack round-trip on small inputs,
packed-step computation on a known small simrec,
tower-bound dominance check on a known small simrec.

## Data flow: the `simrec` case in detail

Given `KMor1.simrec i h g` at level ≤ 2:

1. Recurse on each `h j` (level ≤ 1) and `g j`
   (level ≤ 1), producing `h_j_ER : ERMor1 a` and
   `g_j_ER : ERMor1 (a + 1 + (k + 1))`.

2. Build `pack_base : ERMor1 a` whose interpretation
   Szudzik-packs `(h_0_ER ȳ, ..., h_k_ER ȳ)`.

3. Build `pack_step : ERMor1 (a + 2)` whose
   interpretation, given `(prev_packed, x, ȳ)`,
   Szudzik-decodes `prev_packed` into
   `(prev_0, ..., prev_k)`, applies each `g_j_ER` to
   the context `(x, ȳ, prev_0, ..., prev_k)`, and
   Szudzik-repacks the resulting (k+1)-vector.

4. Compute the tower-height bound via `towerHeight`
   applied to the Szudzik-packed step term, then
   compose `towerBound` to produce
   `bound : ERMor1 (a + 1)`.

5. Apply `ERMor1.boundedRec pack_base pack_step bound`
   to obtain `packed_recursion : ERMor1 (a + 1)`.

6. Compose with `kSimSzudzikUnpack i` to project the
   `i`-th component, giving the final
   `ERMor1 (a + 1)`.

The interp-preservation proof at this case composes:

- `kSimSzudzikUnpack_interp_pack` (round-trip).
- `boundedRec_eq_natRec_of_bounded` (existing
  `Utilities/ERArith.lean`) reducing `boundedRec`
  to plain `Nat.rec` when the bound dominates.
- The recursive interp-preservation hypothesis on
  each `h j` and `g j`.
- The `simrecVec` definition from
  `LawvereKSimInterp.lean` (Phase 1) characterising
  the K^sim simrec's interp.

## Compositional discipline

Per the bottom-up named-composite discipline (CLAUDE.md)
and the P10 interpret-and-verify principle from the
master design document:

- Every helper in C5 is a separately named `def` with an
  `@[simp]`-tagged interp lemma stating its closed-form
  behaviour.  No anonymous let-bindings or inline
  definitions for non-trivial composites.
- The interp-preservation proofs use these named-property
  lemmas as composition primitives.  Larger proofs
  reason about behaviour, not atom-level decomposition.
- `lake build` runs cleanly after each helper landing,
  before the next dependent helper is added.

This pattern was followed throughout Phase 1 and the
existing Phase 2 utility infrastructure.  It is the
standard for the project.

## Tooling note

The Lean 4 implementation can use the Lean MCP skills
for goal inspection (`lean_goal`), tactic search
(`lean_multi_attempt`), and proof-completion under the
`lean4` plugin's deep-search route (the `*-filler-deep`
skill).  The implementation plan should mention these as
available to implementer subagents — they are
particularly relevant for `boundedRec`'s
well-definedness proof obligations and for the Szudzik
round-trip lemmas.

## File structure

- **Modify**: `GebLean/LawvereKSimQuot.lean` — refactor
  `KMorNQuo.atDepth` to Setoid-quotient (C1).
- **Create**: `GebLean/Utilities/KSimSzudzikSimrec.lean`
  — C5 helpers.
- **Create**: `GebLean/LawvereKSimER.lean` — `kToER`,
  `kToERN`, interp-preservation theorems, functor
  `kToERFunctor` (C2–C4, C6).
- **Create**: `GebLeanTests/LawvereKSimER.lean` — C7
  tests.
- **Modify**: `GebLean.lean` — re-export new modules.
- **Modify**: `GebLeanTests.lean` — register new test
  module.

## Out of scope

- Backward translation `erToK` (sub-project 4).
- URM machinery and Ackermann bound (sub-projects 2
  and 3).
- The categorical equivalence assembly (sub-project 4).
- Direct testing of `KSimMor 2 ≌ LawvereERCat` as a
  pair of mutually-inverse functors — both directions
  are needed first.

## Open questions

None at design time.  Implementation may surface
specific tactic-level issues (`boundedRec`'s
well-definedness obligations, `Quotient.lift`
plumbing for the functor) that the implementation plan
will address with concrete pseudo-code and tactic
recipes.
