# Option E Implementation Plan: Bounded NatBT with ER-on-the-Nose Equivalence

> Use `superpowers:subagent-driven-development` to execute
> task-by-task.  Steps use checkbox (`- [ ]`) syntax.

**Design spec**:
`docs/superpowers/specs/2026-04-18-option-e-bounded-natbt-design.md`.

**Supersedes**:
`2026-04-18-lawvere-natramified-two-stage.md` (NatRamified
intermediate, abandoned).

---

## Project rules (from CLAUDE.md)

* `lake build` and `lake test` after every change.  Never `lake
  clean` or `lake env lean`.
* Zero warnings; no `sorry` / `admit` / `Classical` /
  `noncomputable` / `axiom`.  80-char lines.
* Forbidden words in persistent writing: fundamental, actually,
  key, insight, core, advanced, complex, complicated, simple,
  advantage, benefit, important, challenge, yes, wait, hmm,
  sorry, careful, difficult, blocked, incomplete, future, issue,
  problem, block.
* `Co-Authored-By: Claude Opus 4.7 (1M context)
  <noreply@anthropic.com>` trailer on every commit.

---

## Stage 1: Layer 0 — Nat-level ER-style helpers

### Task 1.1: `Nat.foldBTLOnCodeERStyle` definition

* Create `GebLean/Utilities/NatERStyle.lean`.  Add import to
  `GebLean/Utilities.lean`.
* Add helper definitions:

```lean
/-- ER-style course-of-values fold on a Gödel code, mirroring
`ERMor1.foldBTLOnCode`'s β-witness-search semantics at the Nat
level.  Returns the trace value when the supplied bound is
pointwise adequate and counter-monotonic; the witness-search
fallback otherwise. -/
def Nat.boundedRecRangeAt (boundCode : ℕ) (code : ℕ) : ℕ :=
  ((code + boundCode + 3).factorial)
    ^ ((code + boundCode + 3).factorial) + 1

/-- Bounded search returning the least j < range with pred j =
true, else range + 1. -/
def Nat.boundedSearchAt (range : ℕ) (pred : ℕ → Bool) : ℕ := ...

/-- Per-position β-witness predicate. -/
def Nat.foldBTLPredAtIndex
    (baseLeaf : ℕ → ℕ) (stepNode : ℕ → ℕ → ℕ)
    (cand : ℕ) (j : ℕ) : Bool := ...

/-- Top-level Nat-style fold combinator. -/
def Nat.foldBTLOnCodeERStyle
    (baseLeaf : ℕ → ℕ) (stepNode : ℕ → ℕ → ℕ)
    (bound : ℕ → ℕ) (code : ℕ) : ℕ := ...

/-- Same shape for primitive recursion. -/
def Nat.boundedRecERStyle
    (base : ℕ) (step : ℕ → ℕ → ℕ)
    (bound : ℕ → ℕ) (n : ℕ) : ℕ := ...
```

* Build, commit `Add Layer 0 Nat-level ER-style fold helpers`.

### Task 1.2: Soundness — `Nat.foldBTLOnCodeERStyle = ER.foldBTLOnCode.interp`

* Add theorem
  `ERMor1.interp_foldBTLOnCode_eq_natFoldBTLOnCodeERStyle`:

```lean
theorem ERMor1.interp_foldBTLOnCode_eq_natFoldBTLOnCodeERStyle
    {k : ℕ}
    (baseLeaf : ERMor1 (k + 1)) (stepNode : ERMor1 (k + 2))
    (bound : ERMor1 (k + 1)) (ctx : Fin (k + 1) → ℕ) :
    (ERMor1.foldBTLOnCode baseLeaf stepNode bound).interp ctx
      = Nat.foldBTLOnCodeERStyle
        (fun lbl => baseLeaf.interp (Fin.cons lbl (Fin.tail ctx)))
        (fun l r => stepNode.interp
          (Fin.cons l (Fin.cons r (Fin.tail ctx))))
        (fun j => bound.interp (Fin.cons j (Fin.tail ctx)))
        (ctx 0)
```

  Proof structure: case-split on whether the witness exists.
  Adequate case uses existing
  `interp_foldBTLOnCode_of_bounded`.  Non-adequate case shows
  ER's `boundedSearch` returns sentinel `B + 1`, hence
  `betaAtCode` evaluates to a specific Gödel-arithmetic value
  matching `Nat.boundedSearchAt`'s sentinel behavior.

* Mirror for `boundedRec`:
  `ERMor1.interp_boundedRec_eq_natBoundedRecERStyle`.

* Build, commit `Prove Layer 0 ER-soundness theorems`.

---

## Stage 2: Bounded NatBT inductive + interp

### Task 2.1: Create `LawvereNatBTBounded.lean` skeleton

* Create the file with imports + namespace + docstring.
* Reuse `BTL`, `NatBTSort` from `LawvereNatBT.lean` via import.
* Add to `GebLean.lean` in alphabetical position.
* Build, commit `Add LawvereNatBTBounded skeleton`.

### Task 2.2: Define `NatBTMor1` with bounded constructors

* In the new file, define `NatBTMor1` with all 16 constructors:
  zero, succ, natProj, sub, compNat, bsum, bprod, leafBT,
  nodeBT, btProj, compBT, foldBTNat (with `bound` parameter),
  foldBTBT (with `bound`), boundedNatRec, encodeBT, decodeBT.
* Mirror the existing `LawvereNatBT.lean` constructor list, with
  the three fold/recursion constructors taking an additional
  `bound : NatBTMor1 (nm.1 + 1, nm.2) .nat` parameter.
* Build, commit `Define bounded NatBTMor1 inductive`.

### Task 2.3: Define `NatBTMor1.interp` via Layer 0 helpers

* Standard interp for non-fold cases.
* For fold cases, delegate to `Nat.foldBTLOnCodeERStyle` and
  `Nat.boundedRecERStyle`.  Specifically:

```lean
| _, _, NatBTMor1.foldBTNat baseLeaf stepNode tree bound,
      ctxN, ctxB =>
    Nat.foldBTLOnCodeERStyle
      (fun lbl =>
        NatBTMor1.interp baseLeaf (Fin.cons lbl ctxN) ctxB)
      (fun a b =>
        NatBTMor1.interp stepNode
          (Fin.cons a (Fin.cons b ctxN)) ctxB)
      (fun j =>
        NatBTMor1.interp bound (Fin.cons j ctxN) ctxB)
      (NatBTMor1.interp tree ctxN ctxB).encode
```

* Analogous for `foldBTBT` and `boundedNatRec`.
* Add per-constructor `@[simp]` lemmas.
* Build + test, commit `Add bounded NatBTMor1.interp`.

---

## Stage 3: Quotient + Category + Products

### Task 3.1: `NatBTMorN`, identity, composition, quotient

* Create `GebLean/LawvereNatBTBoundedQuot.lean`.
* Mirror existing `LawvereNatBTQuot.lean` structure for the
  bounded inductive.
* Build + test, commit
  `Add NatBTMorN, NatBTMorNQuo, Category instance`.

### Task 3.2: `HasChosenFiniteProducts` + interp functor

* In the same file, define products.
* Create `GebLean/LawvereNatBTBoundedInterp.lean` with faithful
  interp functor.
* Build + test, commit `Add bounded NatBT products + interp functor`.

### Task 3.3: `m = 0` subcategory

* Create `GebLean/LawvereNatBTBounded0.lean` mirroring
  `LawvereNatBT0.lean`.
* Build, commit `Add LawvereNatBTBounded0Cat full subcategory`.

---

## Stage 4: Layer 1 auto-bound combinators

### Task 4.1: `deriveTraceBound` helper

* Create `GebLean/LawvereNatBTBoundedAuto.lean`.
* Define `deriveTraceBound` for each of the three recursive
  constructors.  Construction: structural recursion mirroring
  `ERMor1.towerHeight`, returning a NatBT term that interprets
  to `tower(towerHeight(step) + ε)(sumCtx + 2)`.
* Build, commit `Add deriveTraceBound for auto-bound combinators`.

### Task 4.2: Auto-bound combinators

* Define `foldBTNatAuto`, `foldBTBTAuto`, `primRecAuto` as
  `def`s emitting raw constructors with `deriveTraceBound`.
* Build, commit
  `Add Layer 1 auto-bound combinators (foldBTNatAuto, ...)`.

### Task 4.3: `@[simp]` correctness lemmas

* For each combinator, prove that its interp equals the
  structural fold / Nat.rec value (no min, no fallback).  Uses:
  - Layer 0 soundness (Stage 1's theorems).
  - `deriveTraceBound`'s adequate-monotonicity (proven in this
    task).
* Build + test, commit
  `Add @[simp] correctness lemmas for auto-bound combinators`.

---

## Stage 5: `LawvereERCat ≃ LawvereNatBTBounded` equivalence

### Task 5.1: Forward `F : ER → NatBTBounded`

* Create `GebLean/LawvereERNatBTBoundedEquiv.lean`.
* Define `ERMor1.toNatBT` using Layer 1 combinators
  (`foldBTNatAuto` for bsum/bprod-like cases).
* Prove interp agreement on the nose via Layer 1's `@[simp]`
  lemmas.
* Build + test, commit `Add ER → NatBTBounded forward functor`.

### Task 5.2: Back-translation `G : NatBTBounded → ER`

* Define `NatBTMor1.toER` mapping every constructor (including
  bounded fold cases) to ER terms.  Fold cases compile to
  `ERMor1.foldBTLOnCode` / `ERMor1.boundedRec`.
* Prove interp agreement on the nose via Layer 0 soundness
  (Task 1.2's theorems).
* Build + test, commit
  `Add NatBTBounded → ER back-translation functor`.

### Task 5.3: Equivalence assembly

* Prove `F ∘ G ≃ id` and `G ∘ F ≃ id` extensionally.
* Assemble `lawvereERNatBTBoundedEquivalence : LawvereERCat
  ≌ LawvereNatBTBounded0Cat`.
* Build + test, commit
  `Prove LawvereERCat ≃ LawvereNatBTBounded0 equivalence`.

---

## Stage 6: Phase 4f transport + tests + tracker

### Task 6.1: Transport non-fullness

* Theorems
  `ackermann_not_natBTBounded_definable`,
  `tetration_not_natBTBounded_definable` via the equivalence.
* Commit `Transport Phase 4f non-fullness to NatBTBounded`.

### Task 6.2: Tests

* Create `GebLeanTests/LawvereNatBTBounded.lean`,
  `LawvereNatBTBoundedAuto.lean`,
  `LawvereERNatBTBoundedEquiv.lean`.
* Add `#guard`s exercising raw constructors, auto-bound
  combinators, and round-trip through the equivalence.
* Commit `Add Option E test suite`.

### Task 6.3: Tracker update

* Update `.session/workstreams/lawvere-elementary-recursive.md`
  with completion of all 6 stages.
* Commit `Workstream tracker: Option E equivalence chain complete`.

---

## Completion criteria

1. Stage 1: Layer 0 helpers + ER soundness committed.
2. Stage 2: bounded NatBT inductive + interp committed.
3. Stage 3: categorical machinery committed.
4. Stage 4: Layer 1 combinators + `@[simp]` correctness committed.
5. Stage 5: `LawvereERCat ≃ LawvereNatBTBounded0Cat` proved.
6. Stage 6: Phase 4f transported; tests pass; tracker updated.
7. All builds clean; all tests pass.
