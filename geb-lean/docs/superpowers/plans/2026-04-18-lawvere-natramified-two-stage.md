# LawvereNatRamified Two-Stage Equivalence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax.

**Goal**: build `LawvereERCat ≃ LawvereNatRamified ≃
LawvereNatBTRamified` via two on-the-nose categorical
equivalences with no user-supplied bound parameters.

**Supersedes**:
`2026-04-18-lawvere-natbt-two-stage.md` (bounded intermediate,
abandoned).

**Design spec**:
`docs/superpowers/specs/2026-04-18-lawvere-natramified-two-stage-design.md`.

**Tech stack**: Lean 4, mathlib.  Builds on `LawvereER`,
`LawvereERQuot`, `Utilities/ERArith`, `Utilities/ERTreeArith`,
`LawvereERBoundComputable`.  Reuses `BTL` and friends from
`LawvereNatBT.lean` (renamed in Stage F).

---

## Project rules (from CLAUDE.md)

* `lake build` and `lake test` after every code change.  Never
  `lake clean` or `lake env lean`.
* Zero warnings; no `sorry` / `admit` / `Classical` /
  `noncomputable` / `axiom`.  80-char lines.  All code under
  `namespace GebLean … end GebLean`.
* Forbidden words in persistent writing: fundamental, actually,
  key, insight, core, advanced, complex, complicated, simple,
  advantage, benefit, important, challenge, yes, wait, hmm,
  sorry, careful, difficult, blocked, incomplete, future, issue,
  problem, block.
* `Co-Authored-By: Claude Opus 4.7 (1M context)
  <noreply@anthropic.com>` trailer on every commit.

---

## Stage A: `LawvereNatRamified` definition

### Task A1: `Tier` and `NatRamifiedMor1` inductive

* Create `GebLean/LawvereNatRamified.lean`.
* Add `import GebLean.LawvereNatRamified` to `GebLean.lean` in
  alphabetical position.
* Define:

```lean
inductive Tier : Type
  | nonRec | mayRec
  deriving DecidableEq, Repr, Inhabited

def Tier.max : Tier → Tier → Tier
  | .nonRec, .nonRec => .nonRec
  | _, _ => .mayRec
```

Plus `@[simp]` lemmas for `Tier.max` cases.

* Define `NatRamifiedMor1 : ℕ → Tier → Type` with constructors
  per the design sketch (zero, succ, proj, sub, add, mul, comp,
  natMatch, foldMutNat).
* `lake build`, commit
  `Add Tier and NatRamifiedMor1 inductive`.

### Task A2: `NatRamifiedMor1.interp`

* Add `interp : NatRamifiedMor1 n t → (Fin n → ℕ) → ℕ` using
  `Nat.rec` for `foldMutNat`, mathlib `+`/`*` for `add`/`mul`.
* Add per-constructor `@[simp]` lemmas (rfl-style).
* `lake build && lake test`, commit
  `Add NatRamifiedMor1.interp with simp lemmas`.

### Task A3: `NatRamifiedMorN`, identity, composition

* Define `NatRamifiedMorN n n' := Fin n' → Σ t, NatRamifiedMor1 n t`
  or similar (decide tier-erasure approach: probably tier-erase
  at the tuple level since downstream we don't track tiers
  per-component).  Recommended: `NatRamifiedMorN n n' :=
  Fin n' → NatRamifiedMor1Erased n` where `NatRamifiedMor1Erased
  n := Σ t, NatRamifiedMor1 n t`.
* Define `id`, `comp`, `interp` on tuples.
* `lake build`, commit `Add NatRamifiedMorN tuples and operations`.

### Task A4: Quotient + `Category` instance

* Create `GebLean/LawvereNatRamifiedQuot.lean`.
* Define `natRamifiedMorNRel` (extensional equality of interp).
* Define `NatRamifiedMorNQuo`, lift `id` and `comp`, prove
  category laws, instance `Category LawvereNatRamifiedCat`.
* `lake build && lake test`, commit
  `Add LawvereNatRamifiedCat category`.

### Task A5: `HasChosenFiniteProducts`

* In the same file, define `terminal`, `fst`, `snd`, `pair`,
  prove universal properties.
* `lake build`, commit
  `Add HasChosenFiniteProducts on LawvereNatRamifiedCat`.

### Task A6: Interp functor + faithful + tests

* Create `GebLean/LawvereNatRamifiedInterp.lean`: define
  `natRamifiedInterpFunctor : LawvereNatRamifiedCat ⥤ Type`,
  prove `Faithful`.
* Create `GebLeanTests/LawvereNatRamified.lean` with `#guard`s
  exercising each constructor.
* `lake build && lake test`, commit
  `Add interp functor and Stage A tests`.

---

## Stage B: `LawvereERCat ≃ LawvereNatRamified`

### Task B1: Forward functor `F : ER → NatRamified` skeleton

* Create `GebLean/LawvereERNatRamifiedEquiv.lean`.
* Add import to `GebLean.lean`.
* Define `ERMor1.toRamified : ERMor1 n → NatRamifiedMor1 n _`.
  Cases: zero, succ, proj, sub, comp, bsum, bprod.  For bsum,
  use `foldMutNat` with appropriate base/step (sum
  accumulator); for bprod, use `foldMutNat` with mul/1.
* `lake build`, commit `Add ER → NatRamified forward translation`.

### Task B2: Forward functor: prove `interp` agreement

* Theorem
  `ERMor1.toRamified_interp : t.toRamified.interp ctx = t.interp ctx`.
* Mostly direct by structural induction; bsum/bprod cases need
  `foldMutNat`'s interp unfolded to the accumulator pattern.
* `lake build && lake test`, commit `Prove ER → NatRamified
  preserves interp`.

### Task B3: Forward functor: lift to tuples and quotient

* `ERMorN.toRamified : ERMorN n m → NatRamifiedMorN n m`.
* Prove well-defined on the quotient (extensionality).
* Define `erToRamifiedFunctor : LawvereERCat ⥤
  LawvereNatRamifiedCat`.  Verify `map_id`, `map_comp`.
* `lake build`, commit `Define erToRamifiedFunctor`.

### Task B4: Back-translation `G : NatRamified → ER`

* Define `NatRamifiedMor1.toER : NatRamifiedMor1 n _ → ERMor1 n`.
* Cases: zero, succ, proj, sub, add (via `bsum 1`), mul (via
  `bsum (proj 1)`), comp, natMatch, foldMutNat.
* For `foldMutNat base step k`: use `ERMor1.boundedRec
  base.toER step.toER (siteBound)`.  Define `siteBound :
  ERMor1 (n + 1)` from `step.toER.towerHeight`.
* `lake build`, commit
  `Add NatRamified → ER back-translation`.

### Task B5: Back-translation: prove `interp` agreement

* Theorem `NatRamifiedMor1.toER_interp : ∀ t ctx,
  t.toER.interp ctx = t.interp ctx`.
* For `foldMutNat`: discharge `interp_boundedRec_of_bounded`'s
  hypotheses using `siteBound`'s adequate-monotonicity
  (`siteBound_dominates` and `siteBound_monotonic` lemmas to be
  proved).
* `lake build && lake test`, commit `Prove NatRamified → ER
  preserves interp`.

### Task B6: Back-translation: lift to tuples and quotient

* `NatRamifiedMorN.toER`, prove well-defined, define
  `ramifiedToERFunctor : LawvereNatRamifiedCat ⥤ LawvereERCat`.
* `lake build`, commit `Define ramifiedToERFunctor`.

### Task B7: Equivalence assembly

* Prove `F ∘ G ≃ id` and `G ∘ F ≃ id` (as natural isomorphisms,
  by extensional equality).
* Assemble `lawvereERNatRamifiedEquivalence : LawvereERCat ≌
  LawvereNatRamifiedCat`.
* `lake build && lake test`, commit
  `Prove LawvereERCat ≃ LawvereNatRamifiedCat`.

---

## Stage C: `LawvereNatBTRamified` definition

### Task C1: `NatBTSort`, `NatBTRamifiedMor1` inductive

* Create `GebLean/LawvereNatBTRamified.lean`.
* `NatBTSort` already exists in `LawvereNatBT.lean` — reuse via
  import.  (Or extract to a utility file if cleaner; decide
  during implementation.)
* Define `NatBTRamifiedMor1 : (ℕ × ℕ) → NatBTSort → Tier → Type`
  with all constructors (Nat-side: as in NatRamified;
  BT-side: leafBT, nodeBT, btProj, btMatch, foldMutBT,
  encodeBT, decodeBT).
* `lake build`, commit `Define NatBTRamifiedMor1 inductive`.

### Task C2: `interp` + simp lemmas

* `interp : NatBTRamifiedMor1 nm σ t → (Fin nm.1 → ℕ) →
  (Fin nm.2 → BTL) → σ.carrier` with `BTL.fold` for foldMutBT.
* Per-constructor `@[simp]` lemmas.
* `lake build && lake test`, commit
  `Add NatBTRamifiedMor1.interp with simp lemmas`.

### Task C3: Tuples, quotient, category

* Create `GebLean/LawvereNatBTRamifiedQuot.lean`.
* `NatBTRamifiedMorN`, identity, composition, quotient.
* `Category LawvereNatBTRamifiedCat` instance.
* `lake build`, commit `Add LawvereNatBTRamifiedCat category`.

### Task C4: `HasChosenFiniteProducts` + interp functor

* Same file: products via concatenation of arities.
* Create `GebLean/LawvereNatBTRamifiedInterp.lean` with faithful
  interp functor.
* Create `GebLeanTests/LawvereNatBTRamified.lean`.
* `lake build && lake test`, commit
  `Add NatBTRamified products, interp functor, tests`.

---

## Stage D: `LawvereNatRamified ≃ LawvereNatBTRamified`

### Task D1: Forward inclusion `H : NatRamified → NatBTRamified`

* Create `GebLean/LawvereNatRamifiedNatBTRamifiedEquiv.lean`.
* Define `NatRamifiedMor1.toNatBT : NatRamifiedMor1 n _ →
  NatBTRamifiedMor1 (n, 0) .nat _`.  Structural inclusion.
* Lift to tuples and prove `interp` agreement.
* Define `natRamifiedToNatBTFunctor : LawvereNatRamifiedCat ⥤
  LawvereNatBTRamifiedCat` (objects `n ↦ (n, 0)`).
* `lake build`, commit `Add NatRamified → NatBTRamified inclusion`.

### Task D2: Back-translation `K` (m=0 subcategory)

* Define `NatBTRamifiedMor1.toNatRamified` for terms in objects
  of shape `(n, 0)`, using `BTL.encode`/`decode` for BT-using
  parts.
* `foldMutBT` on a tree at code becomes `foldMutNat` over the
  encoded tree, with handlers operating on encoded sub-trees.
* `lake build`, commit
  `Add NatBTRamified → NatRamified back-translation (m=0)`.

### Task D3: Back-translation: prove `interp` agreement

* Use `BTL.encode_decode` and `BTL.decode_encode` round-trip
  lemmas.
* `lake build && lake test`, commit
  `Prove back-translation preserves interp at m=0`.

### Task D4: Equivalence at m=0 subcategory

* Define `LawvereNatBTRamified0Cat` as the m=0 full
  subcategory.
* Assemble `lawvereNatRamifiedNatBTRamified0Equivalence`.
* For full equivalence at all (n, m), defer the Szudzik-pack
  object iso to a follow-up task (note in commit).
* `lake build && lake test`, commit
  `Prove LawvereNatRamifiedCat ≃ LawvereNatBTRamified0Cat`.

---

## Stage E: Compose chain and transport Phase 4f

### Task E1: Compose

* Create `GebLean/LawvereERNatBTRamifiedEquiv.lean`.
* `lawvereERNatBTRamifiedEquivalence : LawvereERCat ≌
  LawvereNatBTRamified0Cat := lawvereERNatRamifiedEquivalence
  .trans lawvereNatRamifiedNatBTRamified0Equivalence`.
* `lake build`, commit
  `Compose chain LawvereERCat ≃ LawvereNatBTRamified0Cat`.

### Task E2: Transport Phase 4f non-fullness

* Theorems
  `ackermann_not_natBTRamified_definable`,
  `tetration_not_natBTRamified_definable` via the equivalence
  + existing `erInterpFunctor_not_full` /
  `erInterpFunctor_not_full_via_tetration`.
* `lake build`, commit
  `Transport Phase 4f non-fullness to NatBTRamified`.

### Task E3: Tracker update

* Update `.session/workstreams/lawvere-elementary-recursive.md`
  with completion of Stages A-E.
* `lake build`, commit
  `Workstream tracker: NatRamified two-stage chain complete`.

---

## Stage F: Cleanup rename

### Task F1: Rename `LawvereNatBT*` → `LawvereNatBTUnramified*`

* `git mv GebLean/LawvereNatBT.lean
  GebLean/LawvereNatBTUnramified.lean` (and analogous for
  `LawvereNatBT0`, `LawvereNatBTQuot`, `LawvereNatBTInterp`,
  `LawvereNatBTBackTrans`).
* Update all imports and namespace references.
* Update `GebLean.lean` import lines.
* Update header docstrings to note these are the
  non-ramified two-sort theory kept for parallel-development
  reference.
* `lake build && lake test`, commit
  `Rename LawvereNatBT* to LawvereNatBTUnramified*`.

---

## Completion criteria

1. Stage A: `LawvereNatRamified` defined; interp functor
   faithful; tests pass.
2. Stage B: `LawvereERCat ≃ LawvereNatRamified` proved.
3. Stage C: `LawvereNatBTRamified` defined; tests pass.
4. Stage D: `LawvereNatRamified ≃ LawvereNatBTRamified0Cat`
   proved.
5. Stage E: Composed `LawvereERCat ≃ LawvereNatBTRamified0Cat`
   proved; Phase 4f non-fullness transported; tracker updated.
6. Stage F: Existing `LawvereNatBT*` renamed.
7. All builds clean (zero warnings), all tests pass.

---

## Self-review checklist

* Each task has a clear acceptance criterion (build + test
  pass; relevant simp lemmas in place; commit landed).
* No task assumes a step from a different stage's later task.
* Tier discipline preserved at every constructor; back-
  translations always have adequate-monotonic bounds by
  `siteBound` construction.
* No `Classical`, no `noncomputable`, no `axiom`.
* Cleanup pass (Stage F) deferred to last so existing
  references don't break during ramified development.
