# Two-Stage Equivalence Chain for Programmer-Friendly ER with Trees

## Status

Design for a restructuring of the `LawvereNatBT` sub-project.  Replaces
the original single-equivalence plan
(`docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`) with a
two-stage chain.  Informed by the bound-obstruction analysis in the
"ER-Primrec" mini-phase and the user's tier-discipline hypothesis.

## Motivation

The original plan proposed a single equivalence
`LawvereERCat ≃ LawvereNatBTCat` via structural back-translation of
all constructors.  Analysis during Task 14 (back-translation) revealed
two distinct problems:

* The current `foldBTNat` / `foldBTBT` constructors are
  non-ramified state-threaded recursion on trees.  Combined with
  ER-level step functions, they permit computation of tower-of-variable-
  height values, escaping E_3.  Hence the theory as currently defined
  is provably stronger than E_3, and `LawvereERCat ≃ LawvereNatBT`
  cannot hold.
* Even with a bounded-fold primitive that restores E_3 semantics, the
  client-facing API requires explicit bound parameters at every fold
  call site — not programmer-friendly.

The two-stage chain resolves both problems while matching known
mathematical characterizations (Meyer-Ritchie LOOP hierarchy, Leivant
1999 ramified recurrence over free algebras).

## Scope

### In scope

* Restructuring `LawvereNatBT` into a "bounded" intermediate theory.
* Designing a new "ramified" theory with tier-disciplined
  mutual-recursion destructor.
* Equivalence proofs
  `LawvereERCat ≃ LawvereNatBT_bounded ≃ LawvereNatBT_ramified`.

### Out of scope (deferred)

* BT-only adequacy proof (Task 14.5-extended):
  demonstration that arithmetic can be done entirely within
  unlabeled-BT + 0-ary-ℕ subfragment of the ramified theory.  Deferred
  until after the full equivalence chain ships.
* Lex completion of the ramified theory (Stage γ of the original plan).
  Applies to the ramified theory once it stabilizes.

## Design Decisions

### D1. LawvereER is the fixed baseline

`LawvereERCat` remains exactly the Wikipedia-literal ER generators
(`zero`, `succ`, `proj`, `sub`, `comp`, `bsum`, `bprod`) with no
additions.  It is the correctness reference for every other theory in
the project.  The rationale: our measure of any other formulation's
correctness is equivalence with `LawvereERCat`; for that measure to
be meaningful, `LawvereERCat` must be a literal transcription of the
standard.  This anchors the descriptive-complexity correspondence
with higher-order logic noted in Wikipedia's ELEMENTARY article.

Other categories in the project are free to introduce new primitives
so long as equivalence with `LawvereERCat` is provable.

### D2. Priority order: strength > ergonomics > opacity > formalization

In order of severity of failure mode:

1. **Silent strength mismatch** (worst).  If any theory in the chain
   escapes E_3 without intended design, the descriptive-complexity
   correspondence fails and downstream proofs inherit an incorrect
   complexity bound.  Must be prevented mechanically.
2. **Ergonomic friction** (second).  The programmer-friendly theory
   should not require clients to supply bounds or proofs at call
   sites.  Tier discipline replaces client-supplied bounds.
3. **Mathematical opacity** (third).  All else equal, transparency is
   preferred, but a formally-verified type-checker (Lean) provides
   reliability even without transparent semantics.  This is
   tolerable.
4. **Formalization friction** (least).  Lean is bootstrap; the
   long-term plan is for the language to extend itself within the
   language.  Lean foundation becomes maintenance-only once the
   base layer stabilizes.

### D3. Two-stage equivalence chain

```text
LawvereERCat  ≃  LawvereNatBT_bounded  ≃  LawvereNatBT_ramified
(baseline)       (intermediate)            (programmer-friendly target)
```

Each equivalence is a distinct proof with its own load-bearing
machinery.  Staging decomposes the work:

* Equivalence 1 validates that adding trees with explicitly-bounded
  fold operations does not add power beyond E_3.  Uses the existing
  `foldBTLOnCode`, `boundedRec`, `btlEncodeLeaf`/`Node`, and
  `BTL.encode`/`decode` infrastructure.
* Equivalence 2 validates that replacing explicit bounds with tier
  discipline does not change expressive power.  Uses the computable
  `ERMor1.towerHeight` infrastructure.

### D4. Pairing is confined to equivalence 1

Szudzik pairing (via `Nat.pair`, `Gödel β`, and `BTL.encode`) enters
in equivalence 1 because it bridges sort systems (ℕ-only ↔ ℕ+BT).
Equivalence 2 does not use pairing: both theories have ℕ and BT as
native sorts, and the translation is purely a tier-vs-bound exchange
without encoding.

This separation of concerns reuses existing pairing infrastructure
and keeps the ramified-equivalence proof conceptually clean.

### D5. Leivant-standard non-recursive primitive set

The ramified theory's non-recursive fragment includes basic
arithmetic primitives (`add`, `mul`, `sub`) interpreted directly,
not defined via `bsum`/`bprod`.  This matches Leivant's tier-0 +
tier-2 recurrence characterization of E_3 and gives the step
function polynomial growth without requiring iteration inside the
step.

Wikipedia-literal ER derives multiplication from `bsum` / `bprod`.
The ramified theory exposes it as primitive for ergonomic reasons;
equivalence with `LawvereERCat` (transitively via the bounded theory)
still holds because `bsum`/`bprod` compute these functions
extensionally.

### D6. Syntactic inductive with tier parameter

Morphisms are formalized as a 3-indexed inductive:

```lean
inductive NatBTMor1Ramified :
    (dom : NatBTObj) → (cod : NatBTObj) → (tier : Tier) → Type
```

The category-level `Hom` is a dependent pair
`Σ (t : Tier), NatBTMor1Ramified a b t`, making the tier tag
type-level-enforced without duplicating the inductive.

The universal property of the recursive destructor (restricted
parameterized-NatBTObject-recursion) is proved as a theorem on the
syntactic inductive rather than taken as the primary definition.

### D7. Single recursive destructor covering ℕ and BT

A single `foldMut` constructor handles mutual recursion where the
output is any finite product of ℕ's and BT's.  It branches on the
scrutinee sort (ℕ or BT):

* ℕ scrutinee: mutual primitive recursion on ℕ.  Replaces `bsum`,
  `bprod`, and the ERMor1-level `boundedRec`.
* BT scrutinee: mutual structural recursion on BT.  Replaces
  `foldBTNat` and `foldBTBT`.

The step case is restricted to tier `NonRec`; the base case and
scrutinee may be any tier.  This is the Leivant tier-2 ramified
recurrence, viewed categorically as a restricted P(NatBTObject).

### D8. Object structure: pair (n, m)

Objects remain indexed by pairs `(n, m) : ℕ × ℕ` (n ℕ-slots, m
BT-slots).  This gives strict commutativity and associativity of
products — a direct structural property, avoiding the more intricate
reasoning required for arbitrary isomorphism between nested products.

## Architecture

### LawvereERCat (unchanged)

* Morphisms: `ERMor1` inductive with constructors `zero`, `succ`,
  `proj`, `sub`, `comp`, `bsum`, `bprod`.
* Objects: `ℕ`.
* Interpretation: `(Fin n → ℕ) → ℕ`.
* Category: quotient by extensional equality of interpretation.

This is the fixed baseline.  No changes; referenced by the other
theories as their equivalence target.

### LawvereNatBT_bounded (intermediate)

Minimal modification of the current `LawvereNatBT` theory:

* 14 constructors identical to current (`zero`, `succ`, `natProj`,
  `sub`, `compNat`, `bsum`, `bprod`, `leafBT`, `nodeBT`, `btProj`,
  `compBT`, `encodeBT`, `decodeBT`, and one new `boundedNatRec`).
* `foldBTNat` and `foldBTBT` acquire an explicit
  `bound : NatBTMor1 (nm.1 + 1, nm.2) .nat` parameter.
* New constructor `boundedNatRec` for bounded primitive recursion
  on ℕ, mirroring `foldBTNat`'s shape:

  ```lean
  | boundedNatRec {nm : ℕ × ℕ}
      (base : NatBTMor1 nm .nat)
      (step : NatBTMor1 (nm.1 + 2, nm.2) .nat)
      (n : NatBTMor1 nm .nat)
      (bound : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    : NatBTMor1 nm .nat
  ```

* Interpretation: uses `Nat.foldBTLOnCode` truncated by the bound
  (for `foldBTNat`), `BTL.decode` of the bounded-encoded-fold (for
  `foldBTBT`), and the ERMor1 `boundedRec` semantics for
  `boundedNatRec`.
* Category structure unchanged: quotient by extensional equality.

This theory is by construction in E_3.  It is a proof-convenience
intermediate, not a user-facing API.

### LawvereNatBT_ramified (target)

New module.  Morphisms indexed by domain, codomain, and tier tag:

```lean
inductive Tier : Type where
  | nonRec  -- term contains no recursive destructor
  | mayRec  -- term may contain recursive destructors

inductive NatBTMor1Ramified :
    (dom : NatBTObj) → (cod : NatBTObj) → (tier : Tier) → Type
  -- Non-recursive primitives (all tier `NonRec`):
  | zero ... : NatBTMor1Ramified ... NonRec
  | succ ... : NatBTMor1Ramified ... NonRec
  | natProj ... : NatBTMor1Ramified ... NonRec
  | sub ... : NatBTMor1Ramified ... NonRec
  | add ... : NatBTMor1Ramified ... NonRec  -- NEW
  | mul ... : NatBTMor1Ramified ... NonRec  -- NEW
  | natMatch ... : NatBTMor1Ramified ... ...  -- non-recursive case
  | leafBT ... : NatBTMor1Ramified ... NonRec
  | nodeBT ... : NatBTMor1Ramified ... NonRec
  | btProj ... : NatBTMor1Ramified ... NonRec
  | btMatch ... : NatBTMor1Ramified ... ...  -- non-recursive case
  | natProd*, natDestr* : ... -- product structure
  -- Composition with tier propagation:
  | comp {t1 t2 : Tier} ...
    : NatBTMor1Ramified a c (Tier.max t1 t2)
  -- Recursive destructor (tier `MayRec`):
  | foldMut {dom cod : NatBTObj} (scrut_sort : NatBTSort)
      (base_t : Tier) (scrut_t : Tier)
      (base : NatBTMor1Ramified (baseArgs scrut_sort dom) cod base_t)
      (step : NatBTMor1Ramified (stepArgs scrut_sort dom cod) cod NonRec)
      (scrut : NatBTMor1Ramified dom (singleSortObj scrut_sort) scrut_t)
    : NatBTMor1Ramified dom cod MayRec
```

The category-level `Hom` is `Σ t, NatBTMor1Ramified a b t`.

* The step argument's tier being statically `NonRec` is the tier
  discipline that keeps the theory in E_3.
* The base and scrutinee tiers can be anything, allowing free
  composition.
* `natMatch` and `btMatch` are non-recursive case destructors (one-
  level pattern match); their tier is the max of their handlers'
  tiers.

The interpretation is directly recursive on tree/ℕ structure,
matching the recursion principle of a restricted P(NatBTObject).

### Tier propagation rules

* Every leaf constructor (primitive or constant) is `NonRec`.
* `comp f g` has tier `Tier.max (tier f) (tier g)`.
* `natMatch` / `btMatch` have tier = max over handlers.
* `foldMut` is always `MayRec` regardless of its arguments' tiers.

This mechanical discipline is a direct inductive consequence of the
type-level constraints; no separate invariant need be tracked.

## Equivalence 1: LawvereERCat ≃ LawvereNatBT_bounded

### Functor F : LawvereERCat → LawvereNatBT_bounded (embedding)

* Objects: `n ↦ (n, 0)`.
* Morphisms: each ERMor1 generator maps to the syntactically
  identical NatBTMor1_bounded generator.  Fully-faithful on the ER
  fragment; preserves composition, products, identity.

### Functor G : LawvereNatBT_bounded → LawvereERCat (back-translation)

* Objects: `(n, m) ↦ n + m` (every BT slot encoded via `BTL.encode`
  as a ℕ slot).
* Morphisms: structural back-translation on the inductive:
  * Non-fold constructors: direct structural translation (Task 14a's
    `toERUniform` handles the fold-free fragment).
  * `foldBTNat base step tree bound` → `foldBTLOnCode base.toER
    step.toER bound.toER` composed with `tree.toER_bt` via
    pre-composition.
  * `foldBTBT base step tree bound` → the same shape with BT-valued
    output handled via encoding round-trip.
  * `boundedNatRec base step n bound` → `ERMor1.boundedRec base.toER
    step.toER bound.toER` composed with `n.toER`.
  * `leafBT`/`nodeBT` / `encodeBT` / `decodeBT`: use the existing
    `ERMor1.btlEncodeLeaf` / `btlEncodeNode` primitives and
    `BTL.encode_decode`.

### Load-bearing lemmas (equivalence 1)

* `ERMor1.interp_foldBTLOnCode_of_bounded` — from Task 13 Phase 2,
  already proved.
* `ERMor1.interp_boundedRec_of_bounded` — from Task 12e, already
  proved.
* `BTL.encode_decode` and `BTL.decode_encode` — already proved.
* `Nat.bounded_beta_exists` — from Task 12e.1, already proved.
* Task 14a's `toERUniform_interp_aux` — extends naturally to the
  fold cases now that bounds are explicit.

### Reuse estimate

Approximately 90% of existing infrastructure carries over.  New work:
back-translation of the three bounded fold cases, composition into
the equivalence proof, categorical wrapper.

## Equivalence 2: LawvereNatBT_bounded ≃ LawvereNatBT_ramified

### Functor F21 : LawvereNatBT_ramified → LawvereNatBT_bounded

* Objects: identity.
* Non-fold constructors: direct translation (both theories have
  them with identical semantics).
* `add` and `mul` (ramified primitives): translate via `bsum`/
  `bprod` derivations in the bounded theory.
* `natMatch` / `btMatch`: derived via `sub`/arithmetic /
  `decodeBT`-of-specific-values in the bounded theory, or via a
  derived helper.
* `foldMut` with `scrut_sort = .nat` → `boundedNatRec`.  Bound
  computed structurally from the ramified step's tower height.
* `foldMut` with `scrut_sort = .bt` → `foldBTNat` or `foldBTBT`
  depending on the cod's sort structure.  Bound computed similarly.

### Functor F12 : LawvereNatBT_bounded → LawvereNatBT_ramified

* Objects: identity.
* Non-fold constructors: direct translation.
* `bsum f` → `foldMut (scrut_sort = .nat)` with step `(prev + f
  counter)` (non-recursive since `f`, `+`, and `counter` are all
  `NonRec` after derivation).
* `bprod f` → analogous with `*`.
* `boundedNatRec base step n bound` → `foldMut (scrut_sort = .nat)`
  base=base, step=step, scrut=n; the bound is dropped (ramified
  theory doesn't need it).
* `foldBTNat base step tree bound` → `foldMut (scrut_sort = .bt)`;
  bound dropped.
* `foldBTBT base step tree bound` → similar with BT-valued cod.

### Load-bearing lemmas (equivalence 2)

* **Bound-derivation lemma**: for any `foldMut` with tier-0 (NonRec)
  step of structural tower height `k`, an explicit bound ER term of
  height `~k + const` dominates the fold trace.  Uses the computable
  `ERMor1.towerHeight` and `towerER` machinery from
  `LawvereERBoundComputable.lean`.
* **Tier preservation**: `comp` of NonRec-with-NonRec stays NonRec;
  all other constructors respect the tier rules by direct inductive
  argument.
* **Extensional correctness**: each ramified morphism's
  interpretation equals the corresponding bounded-morphism's
  interpretation.  Structural induction.

### No pairing

Both directions are pure tier/bound management.  Neither Szudzik
pairing nor Gödel β appears in this equivalence's proof.

## File Structure

Conservative renaming: existing filenames retain their names but
their contents refer to the bounded theory.  Each bounded-theory
file gains a brief header comment noting this.  New ramified-theory
files use explicit `Ramified` naming.

### Existing files (bounded theory)

* `GebLean/LawvereNatBT.lean` — `BTL`, `NatBTMor1`, interp.  Adds
  bound parameter to `foldBTNat`/`foldBTBT` and new `boundedNatRec`
  constructor.
* `GebLean/LawvereNatBT0.lean` — `FullSubcategory` on `m = 0`.
  Unchanged except for constructor signatures in downstream uses.
* `GebLean/LawvereNatBTInterp.lean` — interp functor.  Updated for
  new constructor signatures.
* `GebLean/LawvereNatBTQuot.lean` — quotient category.  Unchanged
  except for downstream updates.
* `GebLean/LawvereNatBTBackTrans.lean` — Task 14a's back-translation
  extended to cover the bounded fold cases and `boundedNatRec`.

### New files (ramified theory)

* `GebLean/LawvereNatBTRamified.lean` — `Tier`,
  `NatBTMor1Ramified`, interp.
* `GebLean/LawvereNatBTRamifiedInterp.lean` — interp functor.
* `GebLean/LawvereNatBTRamifiedQuot.lean` — quotient category.
* `GebLean/LawvereNatBTRamifiedBackTrans.lean` — back-translation
  to bounded.

### Equivalence proofs

* `GebLean/LawvereNatBTBoundedEquivER.lean` — equivalence 1.
* `GebLean/LawvereNatBTRamifiedEquivBounded.lean` — equivalence 2.
* `GebLean/LawvereNatBTRamifiedEquivER.lean` — transitive
  composition.

## Task Ordering

The original Stage β's Tasks 14–20 are restructured:

### Stage β.a: bounded-theory refactor

1. Rename existing theory content to reflect "bounded" (comments
   only under conservative renaming).
2. Add `bound` parameters to `foldBTNat`/`foldBTBT`.
3. Add `boundedNatRec` constructor and its interp.
4. Update `LawvereNatBTBackTrans.lean` (Task 14a extension):
   complete `toERUniform` for the three new/modified fold cases,
   using existing `foldBTLOnCode` and `boundedRec` infrastructure.
5. Prove `NatBTMor1.toER_interp` unconditionally (dropping the
   `isFoldFree` hypothesis).

### Stage β.b: LawvereERCat ≃ LawvereNatBT_bounded

1. Define functor `F : LawvereERCat → LawvereNatBT_bounded`
   (embedding).
2. Define functor `G : LawvereNatBT_bounded → LawvereERCat`
   (back-translation via quotient).
3. Prove `F ∘ G = id` and `G ∘ F = id` extensionally.
4. Assemble into the categorical equivalence.

### Stage δ.a: ramified-theory definition

1. Define `Tier`, `NatBTMor1Ramified`, interp.
2. Define interp functor; prove faithful.
3. Define quotient category; prove category laws.

### Stage δ.b: back-translation

1. Define `F21 : LawvereNatBT_ramified → LawvereNatBT_bounded`.
2. Bound-derivation helper: given a tier-0 step, compute an
   adequate bound.  Reuses `ERMor1.towerHeight`.
3. Prove correctness.

### Stage δ.c: forward translation

1. Define `F12 : LawvereNatBT_bounded → LawvereNatBT_ramified`.
2. Prove correctness.

### Stage δ.d: assemble equivalence 2

1. Prove `F21 ∘ F12 = id` and `F12 ∘ F21 = id`.
2. Assemble into categorical equivalence.

### Stage δ.e: compose chain

1. Transitive composition: `LawvereERCat ≃ LawvereNatBT_ramified`.
2. Transport Phase 4f.1 Ackermann non-fullness and Phase 4f.2
   tetration non-elementarity across the full chain.

### Finalization

1. Register module in `GebLean.lean`; workstream-tracker update.

## Relationship to deferred work

### Task 14.5-extended (BT-only adequacy research)

Remains deferred until after Stage δ.e.  The adequacy result (that
the unlabeled-BT + 0-way-ℕ-product subfragment of `LawvereNatBT_
ramified` is already equivalent to `LawvereERCat`) is a stronger
claim about WHICH fragments of the ramified theory suffice, and is
best pursued once the full equivalence chain is stable.

### Stage γ (lex completion)

Applies to the ramified theory once `LawvereERCat ≃
LawvereNatBT_ramified` is proved.  Mirror of `LawvereERLexCat`'s
Phase 4d-4e construction.

### Phase 4g.2 supersession

The superseded Phase 4g.2 (LawvereTreeER ↔ LawvereER equivalence)
remains unnecessary under this design.  The two-stage chain via
`LawvereNatBT_bounded` / `LawvereNatBT_ramified` covers the same
territory without needing the tree-only intermediate.  Phase 4g.1's
`LawvereTreeERCat` remains in the codebase as preserved
infrastructure.

## Open Questions

None at time of writing.  Design questions have been resolved
through the preceding conversation.

## Literature References

* Wikipedia, "Elementary recursive function":
  <https://en.wikipedia.org/wiki/Elementary_recursive_function>.
* Wikipedia, "ELEMENTARY", section "Higher-order logic":
  <https://en.wikipedia.org/wiki/ELEMENTARY#Higher-order_logic>.
* Leivant, D.  "Ramified recurrence and computational complexity
  III: Higher-type recurrence and elementary complexity."  *Annals
  of Pure and Applied Logic* 96 (1999), 209–229.  Tier-2 ramified
  recurrence over free algebras = E_3.  Local copy:
  `.claude/docs/ramified-recurrence-computational-complexity-iii.pdf`.
* Meyer, A. and Ritchie, D.  "The complexity of loop programs."
  *Proc. ACM 22nd National Conference* (1967).  LOOP depth = E_{n+2}
  hierarchy.
* Beckmann, A. and Weiermann, A.  "Characterizing the elementary
  recursive functions by a fragment of Gödel's T."  *Archive for
  Mathematical Logic* 39 (2000), 475–491.
* Szudzik, M.  "An elegant pairing function."
  `.claude/docs/ElegantPairing.pdf`.
